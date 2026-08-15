(** Rust entity <-> generated Lean entity, as ONE record.

    Every correspondence in this module is recorded at the moment the
    translation applies it, by the same call that produces the name the
    translation prints. That is the whole design constraint, and it is not
    stylistic.

    {1 Why}

    A downstream consumer that wants to state the semantic basis of a proof has
    to know which Rust entities the generated Lean stands for. For declarations
    Aeneas translates, [EmitJson] already reports the pair. For everything
    Aeneas implements *intrinsically* it reported nothing, and the two cases are
    not equally invisible:

    - a builtin like [core::num::{u32}::wrapping_add] is decided by a table in
      {!ExtractBuiltin}, so the fact exists and is simply never emitted;
    - a primitive like [u32] was decided by a [match] inside the pretty-printer
      ({!ExtractTypes.extract_literal_type}), so there was no correspondence
      object to emit at all.

    The second is why this module exists rather than a second table beside the
    printer. A separate exported mapping would be a *copy* of the translation
    rule, and a copy can drift: the printer could start emitting [Std.U32']
    while the export still claimed [Std.U32], and nothing would notice. The
    consumer would then be reasoning about a correspondence that was never
    applied.

    {1 The invariant}

    {v
    lean_name_of_literal_type  ---> the string the translation prints
                               \--> the correspondence the evidence reports
    v}

    One function, one value, both uses. [extract_literal_type] must not compute
    a primitive's Lean name any other way, and there is no other way exposed.
    An attempt to make translation and export disagree has to begin by adding a
    second mapping, which is the thing this module exists to prevent. *)

open Pure
open Config

(** How the correspondence was decided. Kept apart because a consumer's trust
    question differs per kind: a builtin is a hand-written Lean model standing
    in for an implementation, while a primitive is the representation choice
    the backend is built around. *)
type kind =
  | Primitive  (** A Rust primitive type. Decided by this module. *)
  | BuiltinType  (** [@ExtractBuiltin] type pattern. *)
  | BuiltinFun  (** [@ExtractBuiltin] function pattern. *)

let kind_to_string (k : kind) : string =
  match k with
  | Primitive -> "primitive"
  | BuiltinType -> "builtin_type"
  | BuiltinFun -> "builtin_fun"

type t = { rust_name : string; lean_name : string; kind : kind }

(* ------------------------------------------------------------------------ *)
(* The accumulator                                                          *)
(*                                                                          *)
(* One translation is one process, so a module-local singleton, matching     *)
(* EmitJson's state. Recording is unconditional rather than gated on         *)
(* -emit-json: the cost is a hashtable insert, and a rule that only fires    *)
(* under a flag is a rule whose behaviour differs between the run you        *)
(* measured and the run you shipped.                                         *)
(* ------------------------------------------------------------------------ *)

let applied : (string * string * string, t) Hashtbl.t = Hashtbl.create 64

let record (c : t) : unit =
  let key = (kind_to_string c.kind, c.rust_name, c.lean_name) in
  if not (Hashtbl.mem applied key) then Hashtbl.add applied key c

(** Every correspondence this translation actually applied, sorted so the
    emitted evidence is stable across runs. *)
let applied_correspondences () : t list =
  Hashtbl.fold (fun _ c acc -> c :: acc) applied []
  |> List.sort (fun a b ->
         match compare (kind_to_string a.kind) (kind_to_string b.kind) with
         | 0 -> compare a.rust_name b.rust_name
         | c -> c)

(* ------------------------------------------------------------------------ *)
(* Primitives                                                               *)
(* ------------------------------------------------------------------------ *)

(** The Rust spelling, from Charon's printer rather than a literal here.

    Deliberately not a string written in this file: the Rust name is Charon's
    to spell, and a consumer joining against LLBC compares against exactly this
    rendering. *)
let rust_name_of_literal_type (ty : literal_type) : string option =
  match ty with
  | TInt ty -> Some (Charon.Print.integer_type_to_string (Signed ty))
  | TUInt ty -> Some (Charon.Print.integer_type_to_string (Unsigned ty))
  | TFloat ty -> Some (Charon.Print.float_type_to_string ty)
  | TBool -> Some "bool"
  | TChar -> Some "char"
  (* Not Rust types. [TPureNat] and [TPureInt] are pure-level constructs the
     translation introduces, so they have no Rust counterpart and must not be
     reported as one — a consumer would then require a correspondence for an
     entity that never existed in the program. *)
  | TPureNat | TPureInt -> None

(** The Lean name for a primitive type, AND the record of that decision.

    {b This is the only place the mapping exists.} Callers print the returned
    string; the correspondence is recorded as a side effect of asking, so a
    caller cannot obtain the name without the evidence being written.

    Non-Lean backends get their name as before and record nothing: the
    correspondence evidence is a Lean-backend artifact, and [-emit-json] is
    already rejected for the others. *)
let lean_name_of_literal_type (ty : literal_type) : string =
  let name =
    match ty with
    | TBool -> ExtractBase.bool_name ()
    | TChar -> ExtractBase.char_name ()
    | TInt int_ty ->
        let prefix = if backend () = Lean then "Std." else "" in
        prefix ^ ExtractBase.int_name (Signed int_ty)
    | TUInt int_ty ->
        let prefix = if backend () = Lean then "Std." else "" in
        prefix ^ ExtractBase.int_name (Unsigned int_ty)
    | TFloat float_ty -> ExtractBase.float_name float_ty
    | TPureNat -> "ℕ"
    | TPureInt -> "ℤ"
  in
  (if backend () = Lean then
     match rust_name_of_literal_type ty with
     | Some rust_name -> record { rust_name; lean_name = name; kind = Primitive }
     | None -> ());
  name

(* ------------------------------------------------------------------------ *)
(* Builtins                                                                 *)
(* ------------------------------------------------------------------------ *)

(** Record a builtin substitution at the point the extraction context binds it.

    Unlike the primitives above, this does not *decide* anything — the decision
    is {!ExtractBuiltin}'s table, and the [extract_name] passed here is the one
    the caller is about to register. It is recorded at the single site where a
    builtin's Rust identity meets its Lean name, so the evidence is "what this
    translation applied" rather than "everything the table contains". A crate
    that never touches [wrapping_add] must not claim it as part of its basis. *)
let record_builtin ~(kind : kind) ~(rust_name : string) ~(lean_name : string) :
    unit =
  if backend () = Lean then record { rust_name; lean_name; kind }
