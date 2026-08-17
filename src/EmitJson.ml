(** Emit translation.json which contains the Aeneas data which connects the Lean
    translation to the Rust code. *)

(** Rust source location of a declaration, taken from LLBC [item_meta.span]. *)
type source = {
  file : string;  (** Path to the Rust source file. *)
  begin_line : int;  (** First line of the declaration. *)
  end_line : int;  (** Last line of the declaration. *)
}
[@@deriving to_yojson]

type loop_info = {
  loop_id_idx : int; [@key "id"]
  loop_pos : int list; [@key "pos"]
  is_body : bool;
}
[@@deriving to_yojson]

(** Lean function declaration. *)
type function_entry = {
  def_id : int;  (** Charon [FunDeclId] reified to a plain int. *)
  lean_name : string;  (** Fully-qualified Lean name. *)
  lean_file : string;  (** Path relative to this manifest's directory. *)
  rust_name : string;  (** Fully-qualified Rust name (from [item_meta.name]). *)
  is_local : bool;
      (** [true] if defined in the current crate, [false] if external. *)
  source : source;  (** Rust source location (from [item_meta.span]). *)
  is_opaque : bool;
      (** [true] when Aeneas extracted the declaration as an axiom. *)
  can_fail : bool;
      (** [true] when the function's return type is wrapped in [Result]. *)
  can_diverge : bool;  (** [true] when the function may not terminate. *)
  is_rec : bool;
      (** [true] when the function is part of a mutually recursive group. *)
  reducible : bool;
      (** [true] when Aeneas marks the Lean def with [@[reducible]]. *)
  loop : loop_info option; [@default None] [@key "loop"]
      (** Present only on loop-wrapper / loop-body entries *)
  parent_lean_name : string option; [@default None]
      (** Present only on loop-wrapper / loop-body entries *)
}
[@@deriving to_yojson]

(** Lean type declaration. *)
type type_entry = {
  def_id : int;
  lean_name : string;
  lean_file : string;
  rust_name : string;
  is_local : bool;
  source : source;
}
[@@deriving to_yojson]

(** Lean global declaration. *)
type global_entry = {
  def_id : int;
  lean_name : string;
  lean_file : string;
  rust_name : string;
  is_local : bool;
  source : source;
  can_fail : bool;
}
[@@deriving to_yojson]

(** Lean trait declaration. *)
type trait_decl_entry = {
  def_id : int;
  lean_name : string;
  lean_file : string;
  rust_name : string;
  is_local : bool;
  source : source;
}
[@@deriving to_yojson]

(** Lean trait implementation. *)
type trait_impl_entry = {
  def_id : int;
  lean_name : string;
  lean_file : string;
  rust_name : string;
  is_local : bool;
  source : source;
  impl_trait_def_id : int;
      (** [TraitDeclId] of the implemented trait. A valid LLBC trait decl but
          has entry in [trait_decls] iff the trait is not builtin. *)
  impl_trait_rust_name : string;
      (** Full Rust path of the implemented trait. *)
  impl_trait_is_builtin : bool;
      (** [true] when the implemented trait is builtin. *)
}
[@@deriving to_yojson]

(** One Rust entity <-> generated Lean entity pair that this translation
    actually applied, from {!Correspondence}.

    These are the correspondences Aeneas implements INTRINSICALLY — primitive
    types it is built around, and builtin patterns it substitutes — as opposed
    to the declarations it translates, which the sections above already report.
    Without them a consumer can see that the generated Lean mentions
    [Std.U32] and cannot learn that it stands for Rust [u32].

    [kind] is carried because the trust question differs: a [builtin_fun] is a
    hand-written Lean model standing in for an implementation, while a
    [primitive] is the representation choice the backend is built around. A
    consumer that collapsed them would be unable to say which of its basis is
    modelled and which is structural. *)
(** One [(Rust variant, Lean constructor)] pair the translation resolved.

    [rust_variant_id] is Charon's [VariantId], an index into the enum
    declaration the enclosing entry's [rust_def] already identifies, so the
    pair [(def_id, rust_variant_id)] is a structured Rust-side identity a
    consumer can join on without parsing anything.

    [rust_variant_rendered] is diagnostics, and its presence is deliberate for
    the same reason [rust_rendered_by_aeneas] is: this correspondence exists at
    all only because the Lean-side extractor matched constructor names against
    Rust variant names, so a consumer that joined on the name would be
    repeating the inference instead of reading its result. *)
type variant_entry = {
  rust_variant_id : int;
  rust_variant_rendered : string;
  lean_constructor_rendered : string;
      (** Resolves under the enclosing entry's [lean_scope_namespaces], like
          [lean_rendered_name]. No canonical form is claimed, for the same
          reason: the producer writes a bare string and does not know which
          namespace it lands in. *)
}
[@@deriving to_yojson]

(** Where a builtin correspondence's Rust side lives in the LLBC. *)
type rust_declaration_identity = {
  section : string;  (** [function] | [type] *)
  def_id : int;
  file : string;
  begin_line : int;
}
[@@deriving to_yojson]

type correspondence_entry = {
  rust_def : rust_declaration_identity option;
      (** {b The Rust-side identity, for a builtin.} Charon's own id, which is
          what a consumer must join on. [null] for a primitive, which is not a
          declaration and has no id — its identity is [rust_primitive] below.

          The span is carried so an id join can be checked against a second
          producer fact rather than trusted, the same discipline the
          declaration sections above follow. *)
  rust_primitive : string option;
      (** {b The Rust-side identity, for a primitive.} Charon's spelling of the
          literal type. [null] for a builtin. *)
  rust_rendered_by_aeneas : string;
      (** Provenance only, and kept precisely because it DISAGREES with
          Charon's rendering of the same declaration
          ([{impl core::cmp::Ord for u32}::cmp] against
          [impl_Ord_for_u32::cmp], on 5 of 16 entries in the first crate this
          was measured on). If those five join while these strings still
          differ, nothing is matching on presentation. **Never a key.** *)
  (* No [@default None]: an explicit `null` says "considered, and the producer
     cannot state one", where an absent field says nothing at all. *)
  lean_canonical_name : string list option;
      (** {b The identity, where the producer can state one.} The absolute Lean
          declaration this translation intends to reference, as components. A
          producer DECLARATION, not a resolver result: Aeneas does not run
          Lean's resolver, so a consumer should look each one up and treat one
          that resolves to nothing as a measurable producer defect.

          [null] for builtins. Their [extract_name] is a bare string with no
          namespace and denotes an Aeneas declaration or a Lean-core one
          depending on the entry — [core.result.Result] is
          [Aeneas.Std.core.result.Result] while [Option] and [Ordering] are
          Lean's own. Asserting a prefix for all of them would be wrong for
          most; resolve the qualified reference below instead. *)
  lean_scope_namespaces : string list list;
      (** The namespaces open where [lean_rendered_name] was written. Together
          they form a complete qualified reference that Lean can resolve
          unambiguously, and the producer knows it exactly. *)
  lean_rendered_name : string;
      (** {b Presentation.} The text that appeared in the generated file, which
          resolves only under that file's [open] clauses. Provenance and
          debugging. **Never a join key** — changing which namespaces are
          opened changes this without changing the correspondence's identity,
          and semantic evidence must not be invalidated by that. *)
  kind : string;  (** [primitive] | [builtin_type] | [builtin_fun]. *)
  variants : variant_entry list option;
      (** {b The semantic payload a type correspondence alone does not carry.}

          For an enum, the [(Rust variant, Lean constructor)] mapping this
          translation resolved. [null] for anything that is not an enum, and
          the distinction matters: [null] means "not an enum", where an empty
          list would mean "an enum with no variants".

          CGR-M2 slice 8P exists because two producer revisions that disagree
          about which Lean constructor Rust [Ok] denotes emitted byte-identical
          correspondences without this field, while one of the two was
          semantically false by an independent native-Rust oracle. A consumer
          building a reuse discriminator from the entry above alone would have
          served evidence established under the valid producer as valid under
          the invalid one. *)
}
[@@deriving to_yojson]

(** One semantic lowering rule this translation exercised, for ONE subject.

    {b DIAGNOSTIC ONLY — NOT A CORRESPONDENCE.} Deliberately a separate key from
    [correspondences] rather than a new [kind] inside it, because a consumer
    must not be able to reach these by widening a match on correspondence kinds.
    See {!AppliedLowering} for why the taxonomy is not yet frozen and why
    [rule_id] names a translator branch rather than a semantic consequence. *)
type applied_lowering_entry = {
  subject_section : string option;
      (** [None] where the event fired outside any declaration. Emitted rather
          than dropped: a census that silently discards unattributed events
          under-reports its own denominator. *)
  subject_def_id : int option;
      (** Charon's id, reified. The join key against [functions]. *)
  subject_loop_id : int option;
      (** A loop is a separate declaration sharing its parent's [def_id]. *)
  rule_id : string;
  rust_operation : string;
  lean_emitted_form : string option;
      (** The surface form the producer chose to print. NOT a claim about what
          that form denotes in the checking environment — the measured case's
          whole finding is that those are different questions. *)
  backend : string;
  occurrences : int;
}
[@@deriving to_yojson]

(** A declaration this translation ERASED, and why.

    {b Not a correspondence, and not a diagnostic either.} A consumer derives its
    requirement population from the charon `.llbc` — the crate BEFORE Aeneas'
    prepasses — while the translation happens after them, so it sees requirements
    for declarations that were deliberately deleted. This is the producer stating
    its own erasures so the consumer can reconcile against a MEASURED population
    rather than a transcribed copy of Aeneas' filter list.

    Reuse-relevant, therefore, in the same way an applied correspondence is: a
    producer that stops erasing something has changed the semantics a proof was
    established under. The consumer decides what enters its reuse identity; the
    span below is emitted as an independent check on the id join and is
    deliberately NOT part of that identity. *)
type withdrawal_entry = {
  section : string;
      (** [trait_decl] | [trait_impl] | [function] | [global] *)
  def_id : int;  (** Charon's id, reified. THE join key. *)
  rust_rendered : string;  (** Charon's rendering. Diagnostics only. *)
  file : string;
  begin_line : int;
      (** [file] and [begin_line] are an INDEPENDENT producer fact about the same
          declaration, so a consumer can check the [def_id] join rather than
          trust it. Deliberately NOT part of the consumer's reuse identity: a
          line number moving is not a change in what was erased. *)
  withdrawal_class : string;
      (** A stable CLASS, not a message. It participates in the consumer's reuse
          identity, and a rendered English sentence would make that identity a
          fact about wording. *)
  matched_pattern : string;
      (** The pattern the filter itself matched on — the producer's own key for
          the decision, taken from the same [find_opt] that performed the
          removal. *)
}
[@@deriving to_yojson]

type envelope = {
  aeneas_version : string;
  charon_version : string;
      (** The version of charon that emitted the [.llbc] input. *)
  crate_name : string; [@key "crate"]
      (** Identifier of the source Rust crate. *)
  functions : function_entry list;
  types : type_entry list;
  globals : global_entry list;
  trait_decls : trait_decl_entry list;
  trait_impls : trait_impl_entry list;
  correspondences : correspondence_entry list;
      (** Intrinsic Rust <-> Lean correspondences applied by this translation.
          Not a dump of the builtin tables: only what was used. *)
  withdrawals : withdrawal_entry list;
      (** Declarations this translation ERASED before translating. The other half
          of what a complete reconciliation needs: every raw LLBC requirement
          must be either observed as a correspondence or accounted for here —
          exactly one of the two. *)
  applied_lowerings : applied_lowering_entry list;
      (** CGR-M2 census. DIAGNOSTIC ONLY: no consumer may derive a
          correspondence, a basis requirement or a serving decision from this
          key. It exists so the distribution of lowering rules over a real
          corpus can decide the taxonomy, instead of one subject deciding it. *)
}
[@@deriving to_yojson]

(* ------------------------------------------------------------------------ *)
(* Mutable accumulator state                                                *)
(*                                                                          *)
(* Lifecycle: [init_if_enabled] at the start of [extract_translated_crate], *)
(* [begin_file_if_enabled] at the top of every [extract_file],              *)
(* [record_*_if_enabled] called from the export-* hooks,                    *)
(* [write_if_enabled] once at the end.                                      *)
(* ------------------------------------------------------------------------ *)

type state = {
  mutable function_entries : function_entry list;
  mutable type_entries : type_entry list;
  mutable global_entries : global_entry list;
  mutable trait_decl_entries : trait_decl_entry list;
  mutable trait_impl_entries : trait_impl_entry list;
  mutable current_lean_file : string;
  mutable current_lean_namespace : string;
  mutable dest_dir : string;
}

let make_state () : state =
  {
    function_entries = [];
    type_entries = [];
    global_entries = [];
    trait_decl_entries = [];
    trait_impl_entries = [];
    current_lean_file = "";
    current_lean_namespace = "";
    dest_dir = "";
  }

(* One Aeneas process translates one crate, so a module-local singleton. *)
let state : state = make_state ()

let init_if_enabled ~(dest_dir : string) : unit =
  if !Config.emit_json then state.dest_dir <- dest_dir

(* ------------------------------------------------------------------------ *)
(* Entry construction                                                       *)
(* ------------------------------------------------------------------------ *)

(** Add current Lean namespace to a short name to form the full Lean name. *)
let full_lean_name (basename : string) : string =
  if state.current_lean_namespace = "" then basename
  else state.current_lean_namespace ^ "." ^ basename

(** Extract the Rust source location (file + line range) from a span. *)
let source_of_span (span : Meta.span) : source =
  let data = span.data in
  let file =
    match data.file.name with
    | Virtual s | Local s | NotReal s -> s
  in
  { file; begin_line = data.beg_loc.line; end_line = data.end_loc.line }

let function_entry_of_fun_decl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.fun_decl) : function_entry =
  let span = def.item_meta.span in
  let lean_name =
    full_lean_name
      (ExtractBase.ctx_get_local_function span def.def_id def.loop_id ctx)
  in
  let parent_lean_name =
    match def.loop_id with
    | None -> None
    | Some _ ->
        Some
          (full_lean_name
             (ExtractBase.ctx_get_local_function span def.def_id None ctx))
  in
  let loop =
    match def.loop_id with
    | None -> None
    | Some (lid, is_body) ->
        Some
          {
            loop_id_idx = Pure.LoopId.to_int lid;
            loop_pos = def.loop_pos;
            is_body;
          }
  in
  let eff = def.signature.fwd_info.effect_info in
  {
    def_id = Pure.FunDeclId.to_int def.def_id;
    lean_name;
    lean_file = state.current_lean_file;
    rust_name = ExtractBase.name_to_string ctx def.item_meta.name;
    is_local = def.item_meta.is_local;
    source = source_of_span span;
    is_opaque = Option.is_none def.body;
    can_fail = eff.can_fail;
    can_diverge = eff.can_diverge;
    is_rec = eff.is_rec;
    reducible = def.backend_attributes.reducible;
    loop;
    parent_lean_name;
  }

let type_entry_of_type_decl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.type_decl) : type_entry =
  let span = def.item_meta.span in
  {
    def_id = Pure.TypeDeclId.to_int def.def_id;
    lean_name =
      full_lean_name (ExtractBase.ctx_get_local_type span def.def_id ctx);
    lean_file = state.current_lean_file;
    rust_name = ExtractBase.name_to_string ctx def.item_meta.name;
    is_local = def.item_meta.is_local;
    source = source_of_span span;
  }

let global_entry_of_global_decl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.global_decl) : global_entry =
  let span = def.item_meta.span in
  {
    def_id = Pure.GlobalDeclId.to_int def.def_id;
    lean_name = full_lean_name (ExtractBase.ctx_get_global span def.def_id ctx);
    lean_file = state.current_lean_file;
    rust_name = ExtractBase.name_to_string ctx def.item_meta.name;
    is_local = def.item_meta.is_local;
    source = source_of_span span;
    can_fail = def.can_fail;
  }

let trait_decl_entry_of_trait_decl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.trait_decl) : trait_decl_entry =
  let span = def.item_meta.span in
  {
    def_id = Pure.TraitDeclId.to_int def.def_id;
    lean_name =
      full_lean_name (ExtractBase.ctx_get_trait_decl span def.def_id ctx);
    lean_file = state.current_lean_file;
    rust_name = ExtractBase.name_to_string ctx def.item_meta.name;
    is_local = def.item_meta.is_local;
    source = source_of_span span;
  }

let trait_impl_entry_of_trait_impl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.trait_impl) : trait_impl_entry =
  let span = def.item_meta.span in
  let impl_trait_id = def.impl_trait.trait_decl_id in
  let impl_trait_decl =
    Pure.TraitDeclId.Map.find impl_trait_id ctx.trans_trait_decls
  in
  {
    def_id = Pure.TraitImplId.to_int def.def_id;
    lean_name =
      full_lean_name (ExtractBase.ctx_get_trait_impl span def.def_id ctx);
    lean_file = state.current_lean_file;
    rust_name = ExtractBase.name_to_string ctx def.item_meta.name;
    is_local = def.item_meta.is_local;
    source = source_of_span span;
    impl_trait_def_id = Pure.TraitDeclId.to_int impl_trait_id;
    impl_trait_rust_name =
      ExtractBase.name_to_string ctx impl_trait_decl.item_meta.name;
    impl_trait_is_builtin = Option.is_some impl_trait_decl.builtin_info;
  }

(* ------------------------------------------------------------------------ *)
(* Pipeline hooks (no-ops when -emit-json is off)                           *)
(* ------------------------------------------------------------------------ *)

let begin_file_if_enabled ~(filename : string) ~(namespace : string) : unit =
  if !Config.emit_json then begin
    (* Record the Lean file relative to dest_dir. *)
    let basename = Filename.basename filename in
    let rel =
      match !Config.subdir with
      | None -> basename
      | Some subdir -> Filename.concat subdir basename
    in
    state.current_lean_file <- rel;
    state.current_lean_namespace <- namespace
  end

let record_fun_if_enabled (ctx : ExtractBase.extraction_ctx)
    (def : Pure.fun_decl) : unit =
  if !Config.emit_json then
    state.function_entries <-
      function_entry_of_fun_decl ctx def :: state.function_entries

let record_type_if_enabled (ctx : ExtractBase.extraction_ctx)
    (def : Pure.type_decl) : unit =
  if !Config.emit_json then
    state.type_entries <- type_entry_of_type_decl ctx def :: state.type_entries

let record_global_if_enabled (ctx : ExtractBase.extraction_ctx)
    (def : Pure.global_decl) : unit =
  if !Config.emit_json then
    state.global_entries <-
      global_entry_of_global_decl ctx def :: state.global_entries

let record_trait_decl_if_enabled (ctx : ExtractBase.extraction_ctx)
    (def : Pure.trait_decl) : unit =
  if !Config.emit_json then
    state.trait_decl_entries <-
      trait_decl_entry_of_trait_decl ctx def :: state.trait_decl_entries

let record_trait_impl_if_enabled (ctx : ExtractBase.extraction_ctx)
    (def : Pure.trait_impl) : unit =
  if !Config.emit_json then
    state.trait_impl_entries <-
      trait_impl_entry_of_trait_impl ctx def :: state.trait_impl_entries

(* ------------------------------------------------------------------------ *)
(* Writing                                                                  *)
(* ------------------------------------------------------------------------ *)

let write (path : string) (env : envelope) : unit =
  let out = open_out path in
  Fun.protect
    ~finally:(fun () -> close_out out)
    (fun () ->
      Yojson.Safe.pretty_to_channel out (envelope_to_yojson env);
      output_char out '\n')

let write_if_enabled ~(crate_name : string) : string option =
  if !Config.emit_json then begin
    let path = Filename.concat state.dest_dir "translation.json" in
    write path
      {
        aeneas_version = Option.value GitVersion.commit ~default:"unknown";
        charon_version = Charon.CharonVersion.supported_charon_version;
        crate_name;
        functions = List.rev state.function_entries;
        types = List.rev state.type_entries;
        globals = List.rev state.global_entries;
        trait_decls = List.rev state.trait_decl_entries;
        trait_impls = List.rev state.trait_impl_entries;
        (* Read straight from the accumulator the TRANSLATION wrote. There is
           no second traversal and no table walk here: if this list and the
           generated Lean ever disagreed, it would have to be because one
           function returned two different answers. *)
        correspondences =
          List.map
            (fun (c : Correspondence.t) ->
              {
                rust_def =
                  (match c.rust_identity with
                  | Correspondence.Declaration d ->
                      Some
                        {
                          section = d.section;
                          def_id = d.def_id;
                          file = d.source_file;
                          begin_line = d.source_begin_line;
                        }
                  | Correspondence.PrimitiveType _ -> None);
                rust_primitive =
                  (match c.rust_identity with
                  | Correspondence.PrimitiveType p -> Some p.spelling
                  | Correspondence.Declaration _ -> None);
                rust_rendered_by_aeneas = c.rust_rendered_by_aeneas;
                lean_canonical_name = c.lean_canonical_name;
                lean_scope_namespaces = c.lean_scope_namespaces;
                lean_rendered_name = c.lean_rendered_name;
                kind = Correspondence.kind_to_string c.kind;
                (* Joined on the same identity key the consumer joins on, from
                   a table the TRANSLATION wrote at the point it resolved the
                   mapping. Not a walk of the builtin table. *)
                variants =
                  Option.map
                    (List.map (fun (v : Correspondence.variant_mapping) ->
                         {
                           rust_variant_id = v.rust_variant_id;
                           rust_variant_rendered = v.rust_variant_rendered;
                           lean_constructor_rendered =
                             v.lean_constructor_rendered;
                         }))
                    (Correspondence.variants_for c.rust_identity);
              })
            (Correspondence.applied_correspondences ());
        (* Read from the accumulator `PrePasses.filter_marker_traits` wrote at the
           point it performed each removal. Not a re-derivation of which
           declarations "would have been" filtered: erasure and its evidence come
           from one decision, the same rule the variant mappings follow. *)
        withdrawals =
          List.map
            (fun (w : Correspondence.withdrawal) ->
              match w.w_rust_identity with
              | Correspondence.Declaration d ->
                  {
                    section = d.section;
                    def_id = d.def_id;
                    rust_rendered = w.w_rust_rendered;
                    file = d.source_file;
                    begin_line = d.source_begin_line;
                    withdrawal_class =
                      Correspondence.withdrawal_class_to_string w.w_class;
                    matched_pattern = w.w_matched_pattern;
                  }
              | Correspondence.PrimitiveType _ ->
                  (* A primitive is not a declaration, so it cannot be erased by
                     a declaration filter. Unreachable by construction. *)
                  [%craise_opt_span] None
                    "a withdrawal was recorded for a primitive type")
            (Correspondence.withdrawals ());
        (* Same discipline, different claim: read straight from the accumulator
           the TRANSLATION wrote, at the branches that made the decisions. No
           table walk, and no re-traversal of the pure AST — a second traversal
           would be a second opinion about what the translation did. *)
        applied_lowerings =
          List.map
            (fun (e : AppliedLowering.event) ->
              {
                subject_section =
                  Option.map (fun (s : AppliedLowering.subject) -> s.section)
                    e.subject;
                subject_def_id =
                  Option.map (fun (s : AppliedLowering.subject) -> s.def_id)
                    e.subject;
                subject_loop_id =
                  Option.bind e.subject
                    (fun (s : AppliedLowering.subject) -> s.loop_id);
                rule_id = e.rule_id;
                rust_operation = e.rust_operation;
                lean_emitted_form = e.lean_emitted_form;
                backend = e.backend;
                occurrences = e.occurrences;
              })
            (AppliedLowering.applied_lowerings ());
      };
    Some path
  end
  else None
