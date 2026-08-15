(** Rust entity <-> generated Lean entity, as ONE record.

    Every correspondence in this module is recorded at the moment the
    translation applies it, by the same call that produces the name the
    translation prints. That is the design constraint, and it is not stylistic.

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

    {1 Identity is not presentation}

    A correspondence carries three Lean-side fields and they mean different
    things.

    {v
    lean_rendered_name     "Std.U32"
        the text that appeared in the generated file. Resolves only under
        that file's `open` clauses. PROVENANCE AND DIAGNOSTICS.

    lean_scope_namespaces  [["Aeneas"]; ["Aeneas";"Std"]; ...]
        the namespaces open where that text was written. Together with the
        rendering this is a complete, unambiguous QUALIFIED REFERENCE, and
        the producer knows it exactly.

    lean_canonical_name    Some ["Aeneas"; "Std"; "U32"]
        the absolute declaration this translation intends to reference.
        IDENTITY. Structured components, never a dotted string.
        {b [None] where the producer cannot state it truthfully} — see below.
    v}

    Conflating rendering with identity is a live defect class in this pipeline
    rather than a hypothetical: the [lean_name] emitted for [FunsExternal]
    entries is a rendering that resolves to nothing at all, and a consumer
    looking it up finds no declaration.

    {b The rendered form must never be used as a join key.} It is a fact about
    the file's imports; changing which namespaces are opened changes it without
    changing the correspondence's identity, and semantic evidence should not be
    invalidated by that.

    Components rather than a dotted string because a Lean name is a list of
    components, some of which may need escaping, and re-splitting a rendered
    string is how a consumer reintroduces the parsing this whole interface
    exists to remove.

    {1 Why [lean_canonical_name] is an option, and not a promise}

    It is what the translation {i intends} to reference. Aeneas does not run
    Lean's resolver, so this is a producer {b declaration}, deliberately
    falsifiable: a consumer looks each one up in the environment that checked
    the proof, and one that resolves to nothing is a measurable producer defect
    rather than a silent one. Calling it a resolved name would claim a lookup
    that never happened.

    It is [None] for builtins, and that is a measurement rather than laziness.
    {!Pure.builtin_type_info} and {!Pure.builtin_fun_info} carry
    [extract_name] as a bare string with no namespace, because it is written
    into a file and left to resolve under that file's opens. Whether it denotes
    an Aeneas declaration or a Lean-core one is not recorded anywhere, and it
    genuinely goes both ways — measured in the environment that checks these
    proofs:

    {v
    core::result::Result  -> "core.result.Result"  Aeneas.Std.core.result.Result
    core::option::Option  -> "Option"              Option          (Lean core)
    core::cmp::Ordering   -> "Ordering"            Ordering        (Lean core)
    v}

    A producer that asserted [Aeneas.Std ++ extract_name] for all of them would
    be wrong for two of the three, and the first version of this module was:
    the resolution check caught [Aeneas.Std.Option], [Aeneas.Std.Ordering] and
    [Aeneas.Std.Bool] as MISSING on its first run. Emitting [None] and letting
    the consumer resolve the qualified reference through Lean puts the answer
    where the authority is, and keeps the producer's claim to what it knows.

    For primitives the producer {i does} know, because it decides the rendering
    itself — scalars are written under the [Std] prefix and live in
    {!lean_std_namespace}; [Bool] and [Char] are written bare and are Lean's
    own. One flag decides both the rendering and the canonical form, so they
    cannot disagree.

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

type t = {
  rust_name : string;
  lean_rendered_name : string;
  lean_scope_namespaces : string list list;
  lean_canonical_name : string list option;
  kind : kind;
}

(* ------------------------------------------------------------------------ *)
(* The Lean namespaces, as data                                             *)
(* ------------------------------------------------------------------------ *)

(** Where the Aeneas Lean library's declarations live.

    Both the generated file's [open] clause and every canonical name below are
    derived from this, for the same reason the primitive mapping has one home:
    a literal `open Aeneas Aeneas.Std …` in the header emitter plus a separate
    `Aeneas.Std` in the exporter would be two copies of one fact. *)
let lean_std_namespace : string list = [ "Aeneas"; "Std" ]

(** The namespaces the generated Lean header opens, in order.

    [Aeneas] is what makes a rendered [Std.U32] denote [Aeneas.Std.U32]. *)
let lean_opened_namespaces : string list list =
  [ [ "Aeneas" ]; lean_std_namespace; [ "Result" ]; [ "ControlFlow" ]; [ "Error" ] ]

let dotted (components : string list) : string = String.concat "." components

(** The exact `open …` line the Lean backend emits. Consumed by
    {!Translate.extract_file}, so the header and the canonical names cannot
    disagree about which namespaces are in scope. *)
let lean_header_open_clause () : string =
  "open " ^ String.concat " " (List.map dotted lean_opened_namespaces)

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
  (* Keyed on identity where there is one, and on the qualified reference
     otherwise — never on the rendering alone, which two different scopes could
     make ambiguous. *)
  let identity =
    match c.lean_canonical_name with
    | Some canonical -> dotted canonical
    | None ->
        String.concat "|"
          (c.lean_rendered_name :: List.map dotted c.lean_scope_namespaces)
  in
  let key = (kind_to_string c.kind, c.rust_name, identity) in
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

(** The bare declaration name of a primitive, with no namespace and no prefix.

    The single place the per-type choice is made. Both the rendered form and
    the canonical components below are built from this one value, so they
    cannot name different declarations. *)
let primitive_base_name (ty : literal_type) : string option =
  match ty with
  | TBool -> Some (ExtractBase.bool_name ())
  | TChar -> Some (ExtractBase.char_name ())
  | TInt int_ty -> Some (ExtractBase.int_name (Signed int_ty))
  | TUInt int_ty -> Some (ExtractBase.int_name (Unsigned int_ty))
  | TFloat float_ty -> Some (ExtractBase.float_name float_ty)
  | TPureNat | TPureInt -> None

(** The Lean name for a primitive type, AND the record of that decision.

    {b This is the only place the mapping exists.} Callers print the returned
    string; the correspondence is recorded as a side effect of asking, so a
    caller cannot obtain the name without the evidence being written.

    Non-Lean backends get their name as before and record nothing: the
    correspondence evidence is a Lean-backend artifact, and [-emit-json] is
    already rejected for the others. *)
let lean_name_of_literal_type (ty : literal_type) : string =
  match primitive_base_name ty with
  | None -> (
      (* Pure-level, no Rust counterpart, nothing to record. *)
      match ty with
      | TPureNat -> "ℕ"
      | TPureInt -> "ℤ"
      | _ -> [%craise_opt_span] None "unreachable: unhandled literal type")
  | Some base ->
      let lean = backend () = Lean in
      (* Scalars are rendered under the `Std` prefix; bool, char and floats are
         rendered bare because they are in scope directly. Both branches build
         the SAME declaration, so canonical components follow the same split. *)
      let scalar =
        match ty with
        | TInt _ | TUInt _ -> true
        | _ -> false
      in
      let rendered = if lean && scalar then "Std." ^ base else base in
      (if lean then
         match rust_name_of_literal_type ty with
         | Some rust_name ->
             record
               {
                 rust_name;
                 lean_rendered_name = rendered;
                 lean_scope_namespaces = lean_opened_namespaces;
                 (* The SAME flag that chose the rendering chooses the
                    declaration, so the two cannot name different things.
                    Scalars live in the Aeneas library; `Bool`, `Char` and the
                    float names are written bare and are Lean's own. *)
                 lean_canonical_name =
                   Some
                     (if scalar then lean_std_namespace @ [ base ] else [ base ]);
                 kind = Primitive;
               }
         | None -> ());
      rendered

(* ------------------------------------------------------------------------ *)
(* Builtins                                                                 *)
(* ------------------------------------------------------------------------ *)

(** Record a builtin substitution at the point the extraction context binds it.

    Unlike the primitives above, this does not *decide* anything — the decision
    is {!ExtractBuiltin}'s table, and the [extract_name] passed here is the one
    the caller is about to register. It is recorded at the single site where a
    builtin's Rust identity meets its Lean name, so the evidence is "what this
    translation applied" rather than "everything the table contains". A crate
    that never touches [wrapping_add] must not claim it as part of its basis.

    No canonical name is claimed. [extract_name] is a bare string with no
    namespace, and whether it denotes an Aeneas declaration or a Lean-core one
    is recorded nowhere — see the module header for the measurement showing it
    goes both ways. What IS emitted is the qualified reference: the rendering
    plus the scope it was written in, which the producer knows exactly and
    which Lean can resolve unambiguously. *)
let record_builtin ~(kind : kind) ~(rust_name : string)
    ~(extract_name : string) : unit =
  if backend () = Lean then
    record
      {
        rust_name;
        lean_rendered_name = extract_name;
        lean_scope_namespaces = lean_opened_namespaces;
        lean_canonical_name = None;
        kind;
      }
