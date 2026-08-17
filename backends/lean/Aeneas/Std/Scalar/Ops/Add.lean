import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Addition: Definitions
-/
/- CGR-M2 BODY-ONLY FALSIFIER. NOT AN UPSTREAM CHANGE.

   The operands are swapped. Addition commutes, so this is EXTENSIONALLY THE
   SAME FUNCTION -- and structurally a different body over exactly the same
   constants, so the closure's MEMBERSHIP is unchanged.

   That isolation is the point. The wrapping falsifier changed both the body and
   the membership (46 Aeneas declarations to 35), so a binding computed from
   membership alone discriminated it -- measured by a poison pill that SURVIVED
   dropping declaration values from the identity entirely. This arm has no
   membership signal at all, so only a binding that hashes declaration VALUES
   can see it. -/
def UScalar.add {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  UScalar.tryMk ty (y.val + x.val)

def IScalar.add {ty : IScalarTy} (x y : IScalar ty) : Result (IScalar ty) :=
  IScalar.tryMk ty (x.val + y.val)

def UScalar.try_add {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (add x y)

def IScalar.try_add {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (add x y)

instance {ty} : HAdd (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hAdd x y := UScalar.add x y

instance {ty} : HAdd (IScalar ty) (IScalar ty) (Result (IScalar ty)) where
  hAdd x y := IScalar.add x y


/-!
# Addition: Theorems
-/

theorem UScalar.add_equiv {ty} (x y : UScalar ty) :
  match x + y with
  | ok z => x.val + y.val < 2^ty.numBits ∧
    z.val = x.val + y.val ∧
    z.bv = x.bv + y.bv
  | fail _ => ¬ (UScalar.inBounds ty (x.val + y.val))
  | _ => ⊥ := by
  -- CGR-M2 BODY-ONLY FALSIFIER. Unlike the wrapping falsifier, this lemma is
  -- still TRUE -- addition commutes, so the swapped body denotes the same
  -- function. Only the tactic script breaks, because it was written against the
  -- `x.val + y.val` operand order. Admitted rather than repaired because the
  -- experiment is about the BINDING, not about this proof, and repairing it
  -- would add a second difference to an arm whose whole value is having exactly
  -- one.
  --
  -- The distinction matters and is asserted downstream: the contract under test
  -- must depend on NO sorryAx.
  sorry

theorem IScalar.add_equiv {ty} (x y : IScalar ty) :
  match x + y with
  | ok z =>
    IScalar.inBounds ty (x.val + y.val) ∧
    z.val = x.val + y.val ∧
    z.bv = x.bv + y.bv
  | fail _ => ¬ (IScalar.inBounds ty (x.val + y.val))
  | _ => ⊥ := by
  have : x + y = add x y := by rfl
  rw [this]
  simp [add]
  have h := tryMk_eq ty (↑x + ↑y)
  simp [inBounds] at h
  split at h <;> simp_all
  apply BitVec.eq_of_toInt_eq
  simp
  have := bmod_pow_numBits_eq_of_lt ty (x.val + y.val) (by omega) (by omega)
  simp [*]

/-!
Theorems about the addition, with a specification which uses
integers and bit-vectors.
-/

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.add_bv_spec {ty} {x y : UScalar ty}
  (hmax : ↑x + ↑y ≤ UScalar.max ty) :
  x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ∧ z.bv = x.bv + y.bv ⦄ := by
  have h := @add_equiv ty x y
  split at h <;> simp_all [max]
  have : 0 < 2^ty.numBits := by simp
  omega

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.add_bv_spec {ty}  {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x + ↑y)
  (hmax : ↑x + ↑y ≤ IScalar.max ty) :
  x + y ⦃ z => (↑z : Int) = ↑x + ↑y ∧ z.bv = x.bv + y.bv ⦄ := by
  have h := @add_equiv ty x y
  split at h <;> simp_all [min, max]
  omega

uscalar theorem «%S».add_bv_spec {x y : «%S»} (hmax : x.val + y.val ≤ «%S».max) :
  x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ∧ z.bv = x.bv + y.bv ⦄ :=
  UScalar.add_bv_spec (by scalar_tac)

iscalar theorem «%S».add_bv_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ «%S».max) :
  x + y ⦃ z => (↑z : Int) = ↑x + ↑y ∧ z.bv = x.bv + y.bv ⦄ :=
  IScalar.add_bv_spec (by scalar_tac) (by scalar_tac)

/-!
Theorems about the addition, with a specification which uses
only integers. Those are the most common to use, so we mark them with the
`step` attribute.
-/

/-- Generic theorem - shouldn't be used much -/
@[step]
theorem UScalar.add_spec {ty} {x y : UScalar ty}
  (hmax : ↑x + ↑y ≤ UScalar.max ty) :
  x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ⦄ := by
  have h := @add_equiv ty x y
  split at h <;> simp_all [max]
  have : 0 < 2^ty.numBits := by simp
  omega

/-- Generic theorem - shouldn't be used much -/
@[step]
theorem IScalar.add_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x + ↑y)
  (hmax : ↑x + ↑y ≤ IScalar.max ty) :
  x + y ⦃ z => (↑z : Int) = ↑x + ↑y ⦄ := by
  have h := @add_equiv ty x y
  split at h <;> simp_all [min, max]
  omega

uscalar @[step] theorem «%S».add_spec {x y : «%S»} (hmax : x.val + y.val ≤ «%S».max) :
  x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ⦄ :=
  UScalar.add_spec (by scalar_tac)

iscalar @[step] theorem «%S».add_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ «%S».max) :
  x + y ⦃ z => (↑z : Int) = ↑x + ↑y ⦄ :=
  IScalar.add_spec (by scalar_tac) (by scalar_tac)

end Aeneas.Std
