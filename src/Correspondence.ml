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
    {!Pure.builtin_type_info} and {!Pure.builtin_fun_info} carry [extract_name]
    as a bare string with no namespace, because it is written into a file and
    left to resolve under that file's opens. Whether it denotes an Aeneas
    declaration or a Lean-core one is not recorded anywhere, and it genuinely
    goes both ways — measured in the environment that checks these proofs:

    {v
    core::result::Result  -> "core.result.Result"  Aeneas.Std.core.result.Result
    core::option::Option  -> "Option"              Option          (Lean core)
    core::cmp::Ordering   -> "Ordering"            Ordering        (Lean core)
    v}

    A producer that asserted [Aeneas.Std ++ extract_name] for all of them would
    be wrong for two of the three, and the first version of this module was: the
    resolution check caught [Aeneas.Std.Option], [Aeneas.Std.Ordering] and
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
    a primitive's Lean name any other way, and there is no other way exposed. An
    attempt to make translation and export disagree has to begin by adding a
    second mapping, which is the thing this module exists to prevent. *)

open Pure
open Config

(** How the correspondence was decided. Kept apart because a consumer's trust
    question differs per kind: a builtin is a hand-written Lean model standing
    in for an implementation, while a primitive is the representation choice the
    backend is built around. *)
type kind =
  | Primitive  (** A Rust primitive type. Decided by this module. *)
  | BuiltinType  (** [@ExtractBuiltin] type pattern. *)
  | BuiltinFun  (** [@ExtractBuiltin] function pattern. *)
  | BuiltinTraitDecl
      (** [@ExtractBuiltin] trait-declaration pattern.

          A new MEMBER of this ontology rather than a new ontology: the Rust side
          is a declaration with a Charon id and the Lean side is a hand-written
          model, exactly as for {!BuiltinType} and {!BuiltinFun}. It is separate
          from them because a consumer's trust question differs — a builtin trait
          stands for a whole interface plus its laws, not a single declaration's
          behaviour.

          Measured before being added: the mapping decisions exist
          ({!ExtractBuiltinLean} holds 47 [mk_trait_decl] entries, including the
          [core::ops::function::Fn]/[FnMut]/[FnOnce] family) and there was no
          recording site for any of them, because [record_builtin] was reachable
          only from the type and function paths. Applied by every translation
          that touches a closure, and reported nowhere. *)
  | BuiltinTraitImpl  (** [@ExtractBuiltin] trait-implementation pattern. *)

let kind_to_string (k : kind) : string =
  match k with
  | Primitive -> "primitive"
  | BuiltinType -> "builtin_type"
  | BuiltinFun -> "builtin_fun"
  | BuiltinTraitDecl -> "builtin_trait_decl"
  | BuiltinTraitImpl -> "builtin_trait_impl"

(** How the Rust side of a correspondence is identified.

    Two populations, and the difference is not cosmetic. A builtin stands for a
    DECLARATION that exists in the LLBC, so it has the compiler's own id and
    that id is what a consumer should join on. A primitive is not a declaration
    at all — there is no `u32` decl to point at — so its identity is Charon's
    spelling of the literal type, which both sides already produce with the
    same printer.

    Rendered names are NOT identity. Aeneas and Charon render the same
    declaration differently (`{impl core::cmp::Ord for u32}::cmp` against
    `impl_Ord_for_u32::cmp`), so a consumer joining on the rendering drops
    exactly the trait impls — measured at 5 of 16 on the first crate this was
    tried against. *)
type rust_identity =
  | Declaration of {
      section : string;  (** [function] | [type] *)
      def_id : int;  (** Charon's id, reified. THE join key. *)
      source_file : string;
      source_begin_line : int;
          (** An independent producer fact about the same declaration, so a
              consumer can check the id join rather than trust it — the same
              discipline `EmitJson` applies to translated declarations. *)
    }
  | PrimitiveType of { spelling : string }
      (** Charon's spelling of the literal type. Not a declaration. *)

type t = {
  rust_identity : rust_identity;
  rust_rendered_by_aeneas : string;
      (** Provenance and diagnostics only. Kept precisely BECAUSE it disagrees
          with Charon's rendering: if the five known-divergent entries join
          while these strings still differ, nothing is matching on presentation.
      *)
  lean_rendered_name : string;
  lean_scope_namespaces : string list list;
  lean_canonical_name : string list option;
  kind : kind;
}

let rust_identity_key (id : rust_identity) : string =
  match id with
  | Declaration { section; def_id; _ } -> section ^ "#" ^ string_of_int def_id
  | PrimitiveType { spelling } -> "primitive#" ^ spelling

(* ------------------------------------------------------------------------ *)
(* The Lean namespaces, as data                                             *)
(* ------------------------------------------------------------------------ *)

(** Where the Aeneas Lean library's declarations live.

    Both the generated file's [open] clause and every canonical name below are
    derived from this, for the same reason the primitive mapping has one home: a
    literal `open Aeneas Aeneas.Std …` in the header emitter plus a separate
    `Aeneas.Std` in the exporter would be two copies of one fact. *)
let lean_std_namespace : string list = [ "Aeneas"; "Std" ]

(** The namespaces the generated Lean header opens, in order.

    [Aeneas] is what makes a rendered [Std.U32] denote [Aeneas.Std.U32]. *)
let lean_opened_namespaces : string list list =
  [
    [ "Aeneas" ];
    lean_std_namespace;
    [ "Result" ];
    [ "ControlFlow" ];
    [ "Error" ];
  ]

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
  let key =
    (kind_to_string c.kind, rust_identity_key c.rust_identity, identity)
  in
  if not (Hashtbl.mem applied key) then Hashtbl.add applied key c

(** Every correspondence this translation actually applied, sorted so the
    emitted evidence is stable across runs. *)
let applied_correspondences () : t list =
  Hashtbl.fold (fun _ c acc -> c :: acc) applied []
  |> List.sort (fun a b ->
         match compare (kind_to_string a.kind) (kind_to_string b.kind) with
         | 0 ->
             compare
               (rust_identity_key a.rust_identity)
               (rust_identity_key b.rust_identity)
         | c -> c)

(* ------------------------------------------------------------------------ *)
(* Primitives                                                               *)
(* ------------------------------------------------------------------------ *)

(** The Rust spelling, from Charon's printer rather than a literal here.

    Deliberately not a string written in this file: the Rust name is Charon's to
    spell, and a consumer joining against LLBC compares against exactly this
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

    The single place the per-type choice is made. Both the rendered form and the
    canonical components below are built from this one value, so they cannot
    name different declarations. *)
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
                 rust_identity = PrimitiveType { spelling = rust_name };
                 rust_rendered_by_aeneas = rust_name;
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
    plus the scope it was written in, which the producer knows exactly and which
    Lean can resolve unambiguously.

    The Rust side carries the LLBC [def_id] and the declaration's span. The
    rendered Rust name is kept beside them as provenance and is not identity:
    Aeneas and Charon render the same declaration differently, so a consumer
    that joined on the rendering would drop every trait impl. *)
let record_builtin ~(kind : kind) ~(rust_name : string) ~(extract_name : string)
    ~(section : string) ~(def_id : int) ~(span : Meta.span) : unit =
  if backend () = Lean then
    let data = span.data in
    let source_file =
      match data.file.name with
      | Virtual s | Local s | NotReal s -> s
    in
    record
      {
        rust_identity =
          Declaration
            {
              section;
              def_id;
              source_file;
              source_begin_line = data.beg_loc.line;
            };
        rust_rendered_by_aeneas = rust_name;
        lean_rendered_name = extract_name;
        lean_scope_namespaces = lean_opened_namespaces;
        lean_canonical_name = None;
        kind;
      }

(* ------------------------------------------------------------------------ *)
(* Applied variant correspondences                                          *)
(*                                                                          *)
(* CGR-M2 slice 8P. A type correspondence is NOT the whole semantic fact.   *)
(*                                                                          *)
(* Measured: two producer revisions that map `core::result::Result` to the  *)
(* same Lean type, and disagree about which Lean constructor Rust `Ok`      *)
(* denotes, export BYTE-IDENTICAL correspondences. One of the two is        *)
(* semantically false — an independent native-Rust oracle says so — and no  *)
(* consumer reading this file could tell them apart. A reuse discriminator  *)
(* built on that export would let evidence established under the valid      *)
(* producer be served under the invalid one.                                *)
(*                                                                          *)
(* So the variant mapping is evidence, at the granularity the theorem       *)
(* actually depends on:                                                     *)
(*                                                                          *)
(*     Rust enum type <-> Lean enum type        the pair both revisions share *)
(*     Rust variant   <-> Lean constructor      the pair they differ on       *)
(* ------------------------------------------------------------------------ *)

(** One [(Rust variant, Lean constructor)] pair, as the translation resolved it.

    The Rust side is Charon's [VariantId] reified — an index into the LLBC
    declaration, which is a structured identity the consumer already holds. The
    Rust variant NAME is carried beside it and is diagnostic only, for the same
    reason [rust_rendered_by_aeneas] is: this pipeline has repeatedly measured
    presentation standing in for identity, and this correspondence is the case
    where it did the most damage — the mapping exists at all only because the
    Lean-side extractor matched constructor names against Rust variant names. A
    consumer must not repeat that inference to read the result of it. *)
type variant_mapping = {
  rust_variant_id : int;  (** Charon's [VariantId], reified. THE join key. *)
  rust_variant_rendered : string;  (** Diagnostics. Never a key. *)
  lean_constructor_rendered : string;
      (** The constructor name the translation registered and will print.
          Rendered rather than canonical for the same reason a builtin type's
          [lean_canonical_name] is [None]: it is a bare string resolved under
          the generated file's opens, and the producer does not know which
          namespace it lands in. Resolve it against [lean_scope_namespaces] of
          the enclosing type entry. *)
}

(** Applied variant mappings, keyed by the enclosing type's Rust identity.

    A SECOND table rather than a field on {!t} only because the type
    correspondence is recorded when the type's name is registered and the
    variants are resolved a few lines later in the same function. Both are
    written at their own decision site; neither is reconstructed. {!EmitJson}
    joins them on [rust_identity_key], which is the same key the consumer joins
    on. *)
let applied_variants : (string, variant_mapping list) Hashtbl.t =
  Hashtbl.create 16

(** Record the variant mapping this translation resolved for one enum.

    {b Read the word "resolved".} This is called where the mapping is decided
    and registered into the extraction context — not at the point a constructor
    is printed. So it says the translation resolved this mapping for a type it
    registered, NOT that every variant was applied to a value. An enum
    registered while only one of its variants appears in the program reports
    both, and that is the honest reading rather than a defect.

    Recording at the print site was the alternative and is worse: the evidence
    would become a function of how many times a name was printed, and a mapped
    but unused variant would be silently absent from the semantic basis. *)
let record_variants ~(section : string) ~(def_id : int)
    ~(variants : variant_mapping list) : unit =
  if backend () = Lean then
    let key =
      rust_identity_key
        (Declaration
           { section; def_id; source_file = ""; source_begin_line = 0 })
    in
    match Hashtbl.find_opt applied_variants key with
    | None -> Hashtbl.add applied_variants key variants
    | Some existing when existing = variants -> ()
    | Some _ ->
        (* Two different mappings for one type. Not resolvable by precedence,
           for exactly the reason `index_correspondences` refuses the same
           shape at the declaration bridge: picking either would make the
           semantic basis a fact about iteration order. *)
        [%craise_opt_span] None
          ("two different variant correspondences were resolved for " ^ section
         ^ "#" ^ string_of_int def_id ^ "; refusing to pick one")

(** The variant mapping recorded for a correspondence, if it is an enum. *)
let variants_for (id : rust_identity) : variant_mapping list option =
  Hashtbl.find_opt applied_variants (rust_identity_key id)

(* ------------------------------------------------------------------------ *)
(* Withdrawals: semantic ERASURE as first-class evidence                    *)
(*                                                                          *)
(* CGR-M2 slice 11. A second population, and it is not a correspondence.    *)
(*                                                                          *)
(* Measured: a consumer derives its requirement population from the charon  *)
(* `.llbc` — the crate BEFORE this translator's prepasses — while the       *)
(* translation happens AFTER them. So the consumer sees requirements for    *)
(* declarations the translation deliberately DELETED, and asks for          *)
(* correspondences that cannot exist. `core::marker::Destruct` and its drop *)
(* glue are the measured case.                                             *)
(*                                                                          *)
(* The tempting repair is for the consumer to keep a list of what this      *)
(* translator filters and subtract it. That replaces one bad inference      *)
(*                                                                          *)
(*     the LLBC mentions Destruct, so a Destruct correspondence is required *)
(*                                                                          *)
(* with another                                                             *)
(*                                                                          *)
(*     Destruct is on our copied ignore list, so it does not matter         *)
(*                                                                          *)
(* and a copied list is a second copy of this translator's decision — the   *)
(* thing this module exists to prevent. So the producer REPORTS its own     *)
(* erasures, and the consumer reconciles against a measured population      *)
(* instead of a transcribed one.                                            *)
(*                                                                          *)
(*     >  Semantic application and semantic erasure must EACH produce       *)
(*     >  evidence from the operation itself, not from a second             *)
(*     >  reconstruction of what supposedly happened.                       *)
(* ------------------------------------------------------------------------ *)

(** Why a declaration was erased. A stable CLASS, not a message.

    Stable because it participates in the consumer's reuse identity: a producer
    that stops erasing something, or erases it for a different reason, has
    changed the semantics a proof was established under. A rendered English
    sentence would make that identity a fact about wording. *)
type withdrawal_class =
  | MarkerTraitNoSemanticContent
      (** A compiler-internal marker trait carrying no semantic content relevant
          to verification, plus its impls and associated items. See
          {!PrePasses.filter_marker_traits}, which is where the decision is made
          and where this is recorded. *)

let withdrawal_class_to_string (c : withdrawal_class) : string =
  match c with
  | MarkerTraitNoSemanticContent -> "marker_trait_no_semantic_content"

type withdrawal = {
  w_rust_identity : rust_identity;
      (** The declaration erased. Structured, and the join key. *)
  w_rust_rendered : string;  (** Charon's rendering. Diagnostics only. *)
  w_class : withdrawal_class;
  w_matched_pattern : string;
      (** The filter's OWN key — the pattern that matched.

          Part of the semantic identity rather than a diagnostic, because it is
          what the producer used to decide. It is stable in the way a rendered
          name is not: it is written in the filter, not derived from a printer. *)
}

let withdrawn : (string, withdrawal) Hashtbl.t = Hashtbl.create 32

(** Record one erasure, at the point the declaration is actually removed.

    Unconditional rather than gated on [-emit-json], matching {!record}: a rule
    that only fires under a flag is a rule whose behaviour differs between the
    run that was measured and the run that shipped. Not gated on the backend
    either — an erasure is a fact about the crate, decided before any backend
    is consulted. *)
let record_withdrawal ~(section : string) ~(def_id : int)
    ~(rust_rendered : string) ~(cls : withdrawal_class)
    ~(matched_pattern : string) : unit =
  let identity =
    Declaration { section; def_id; source_file = ""; source_begin_line = 0 }
  in
  let key = rust_identity_key identity in
  if not (Hashtbl.mem withdrawn key) then
    Hashtbl.add withdrawn key
      {
        w_rust_identity = identity;
        w_rust_rendered = rust_rendered;
        w_class = cls;
        w_matched_pattern = matched_pattern;
      }

(** Every declaration this translation erased, sorted for a stable export. *)
let withdrawals () : withdrawal list =
  Hashtbl.fold (fun _ w acc -> w :: acc) withdrawn []
  |> List.sort (fun a b ->
         compare
           (rust_identity_key a.w_rust_identity)
           (rust_identity_key b.w_rust_identity))
