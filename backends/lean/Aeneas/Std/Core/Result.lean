import Aeneas.Extract

namespace Aeneas.Std

/- DELIBERATELY FALSE — CodeGraphite CGR-M2 slice 7, the C1 arm.

   This revision exists to be WRONG in exactly one respect, so that a
   verification pipeline resting on it can be observed resting on it. Do not
   merge it, do not propose it upstream, and do not use this producer for any
   measurement other than the correspondence-drift experiment it was built for.

   Upstream (`d382a18e`) declares no `body` for this type, so Aeneas infers the
   variant correspondence by matching Rust variant names against Lean
   constructor names — `Ok <-> Ok` is a name coincidence promoted to a semantic
   correspondence, not something anyone stated.

   Here the body is stated, and swapped: Rust's `Ok` is declared to correspond
   to Lean's `Err` and vice versa. The inductive below is UNCHANGED, the Rust
   source is unchanged, and so are the LLBC subject identity, the dependency
   relation and the theorem statement. The only thing that moves is what the
   translation believes a Rust `Result` variant MEANS.

   Both `Ok` and `Err` are real constructors, so the extractor's own variant
   validation has no reason to refuse this. It is well-formed and false, which
   is the only kind of mutation worth deploying. -/
@[rust_type "core::result::Result"
  (body := .enum [⟨"Ok", "Err", none⟩, ⟨"Err", "Ok", none⟩])]
inductive core.result.Result (T : Type u) (E : Type v) where
| Ok : T → core.result.Result T E
| Err : E → core.result.Result T E

end Aeneas.Std
