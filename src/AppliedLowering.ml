(** Which SEMANTIC LOWERING RULES this translation actually exercised.

    {b DIAGNOSTIC ONLY.} Nothing in this module is a correspondence, and nothing
    here may be consumed as evidence. It exists to answer one measurement
    question before any evidence schema is committed:

    {v
    which translation decisions does the generated artifact actually depend on,
    and how are they distributed over a real corpus?
    v}

    {1 Why this is not {!Correspondence}}

    {!Correspondence} records a Rust entity paired with the generated Lean
    entity it stands for. Two measurements showed that population is not the
    whole semantic basis, and the second showed the gap is not a missing entry
    but a missing {i kind}:

    - a Rust [u32] comparison used as a branch condition produces a [bool];
    - the generated Lean contains no [Bool] anywhere, and not because a name
      went unprinted — the value never exists. Aeneas emits [v > BOUND] as infix
      notation, and in the checking environment that notation denotes a
      proposition.

    So a consumer asking "is every required Rust entity paired with a Lean
    entity?" gets the right refusal for the wrong reason: the entity [bool] is
    not missing a partner, it is not the unit of the decision at all. The
    decision was {i how a comparison is lowered}.

    Adding a correspondence kind for that on the strength of one subject is how
    the first repair for this went wrong. The taxonomy is still empirical, so
    this module measures the distribution first and names nothing.

    {1 A rule is a translator branch, not a semantic claim}

    [rule_id] identifies {b the branch of this translator that fired}. It does
    not describe the meaning of the result, and that restraint is the point.

    For the measured case the tempting rule name was
    [scalar_comparison_as_proposition]. It is wrong, and wrong in an instructive
    way: Aeneas decided to emit infix [>]. That the result is [Prop]-valued
    follows from [instance {ty} : LT (UScalar ty)] in the Aeneas Lean library,
    and the [Decidable] instance and [ite] that make [if] work are Lean's
    elaboration. Those are facts about the checking environment, not decisions
    this translator made, and one subject is nowhere near enough to freeze where
    that boundary lies. So the rule is [binop_infix_notation] — what the branch
    does — and the Lean-side consequence is left to be measured elsewhere.

    Same discipline for the two rendered fields:

    {v
    rust_operation      what was being translated, as Aeneas renders it.
                        GROUPING AND DIAGNOSTICS.
    lean_emitted_form   the surface form this translation chose to print,
                        taken from the value actually printed.
                        A PRODUCER FACT — the producer chose the notation.
                        NOT a claim about what the notation denotes.
    v}

    The second is knowable exactly and is worth having; conflating it with the
    denotation is the error this module is shaped to avoid.

    {1 Every traversed node emits something}

    Recording only at the four interesting sites — binops, unops, casts,
    switches — would make [other] mean "other among the four sites I thought to
    instrument". A whole lowering class (field projection, indexing, monadic
    binding, pattern binding, loops, trait dispatch) would emit nothing, and
    nothing reads as "no lowering required" rather than "not measured".

    So the expression dispatch itself records a [construct_*] event for every
    node it traverses, and the specific sites layer refinements on top. A
    construct that occurred without any specific rule firing is then a visible
    cell in the producer's own data rather than a caveat someone has to remember
    to write down. *)

type event = {
  subject : subject option;
      (** [None] when an event fires outside any declaration. Kept
          representable rather than dropped: silently discarding unattributed
          events is how a census under-reports its own denominator. *)
  rule_id : string;  (** THE branch of this translator that fired. *)
  rust_operation : string;
      (** What was being translated, as Aeneas renders it. Grouping and
          diagnostics. Never a join key. *)
  lean_emitted_form : string option;
      (** The surface form printed, where the branch chose one. *)
  backend : string;
  occurrences : int;
}

(** Which declaration was being extracted. Structured, and never a rendered
    name.

    [loop_id] is part of the identity rather than folded away: Aeneas extracts a
    loop as a separate [fun_decl] sharing its parent's [def_id], so aggregating
    over [def_id] alone silently double-counts a subject's events. A consumer
    can still sum over loops; it cannot recover the split if the producer threw
    it away. *)
and subject = {
  section : string;  (** [function] — the only section with expressions. *)
  def_id : int;  (** Charon's id, reified. THE join key. *)
  loop_id : int option;
}

let subject_key (s : subject option) : string =
  match s with
  | None -> "unattributed"
  | Some { section; def_id; loop_id } ->
      section ^ "#" ^ string_of_int def_id
      ^ (match loop_id with
        | None -> ""
        | Some l -> "@loop" ^ string_of_int l)

(* ------------------------------------------------------------------------ *)
(* The ambient subject                                                      *)
(*                                                                          *)
(* Expression extraction is a deep recursion that does not carry the        *)
(* enclosing declaration, and threading it through every arm of Extract.ml  *)
(* would be a large diff to a translator this project does not own. A       *)
(* single-process translation makes a module-local ref sound, and it        *)
(* matches how {!Correspondence} and {!EmitJson} already accumulate.        *)
(* ------------------------------------------------------------------------ *)

let current_subject : subject option ref = ref None

let with_subject (s : subject) (f : unit -> 'a) : 'a =
  let saved = !current_subject in
  current_subject := Some s;
  Fun.protect ~finally:(fun () -> current_subject := saved) f

(* ------------------------------------------------------------------------ *)
(* The accumulator                                                          *)
(* ------------------------------------------------------------------------ *)

let events : (string * string * string * string, event) Hashtbl.t =
  Hashtbl.create 256

(** Record one firing. Occurrences accumulate per
    [(subject, rule, operation, emitted form)], because a census of "how much of
    the corpus depends on this rule" needs counts and not a set. *)
let record ~(rule_id : string) ~(rust_operation : string) ?lean_emitted_form ()
    : unit =
  if Config.backend () = Config.Lean then
    let subject = !current_subject in
    let form =
      match lean_emitted_form with
      | None -> ""
      | Some f -> f
    in
    let key = (subject_key subject, rule_id, rust_operation, form) in
    match Hashtbl.find_opt events key with
    | Some e ->
        Hashtbl.replace events key { e with occurrences = e.occurrences + 1 }
    | None ->
        Hashtbl.add events key
          {
            subject;
            rule_id;
            rust_operation;
            lean_emitted_form;
            backend = "Lean";
            occurrences = 1;
          }

(** Every lowering rule this translation exercised, sorted so the emitted
    diagnostic is stable across runs. *)
let applied_lowerings () : event list =
  Hashtbl.fold (fun _ e acc -> e :: acc) events []
  |> List.sort (fun a b ->
         match compare (subject_key a.subject) (subject_key b.subject) with
         | 0 -> (
             match compare a.rule_id b.rule_id with
             | 0 -> compare a.rust_operation b.rust_operation
             | c -> c)
         | c -> c)
