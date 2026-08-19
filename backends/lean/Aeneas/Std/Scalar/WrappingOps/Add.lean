import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Wrapping Add
-/

def UScalar.wrapping_add {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.bv + y.bv ⟩

def IScalar.wrapping_add {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.bv + y.bv ⟩

uscalar @[step_pure_def]
def «%S».wrapping_add (x y : «%S») : «%S» := @UScalar.wrapping_add UScalarTy.«%S» x y

iscalar @[step_pure_def]
def «%S».wrapping_add (x y : «%S») : «%S» := @IScalar.wrapping_add IScalarTy.«%S» x y

/- [core::num::{_}::wrapping_add] -/
uscalar @[step_pure_def]
def core.num.«%S».wrapping_add : «%S» → «%S» → «%S» := @UScalar.wrapping_add UScalarTy.«%S»

/- [core::num::{_}::wrapping_add] -/
iscalar @[step_pure_def]
def core.num.«%S».wrapping_add : «%S» → «%S» → «%S»  := @IScalar.wrapping_add IScalarTy.«%S»

@[simp, bvify] theorem UScalar.wrapping_add_bv_eq {ty} (x y : UScalar ty) :
  (wrapping_add x y).bv = x.bv + y.bv := by
  simp only [wrapping_add]

uscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_add_bv_eq (x y : «%S») :
  («%S».wrapping_add x y).bv = x.bv + y.bv := by
  simp [«%S».wrapping_add]

uscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_add_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).bv = x.bv + y.bv := by
  simp [core.num.«%S».wrapping_add]

@[simp, bvify] theorem IScalar.wrapping_add_bv_eq {ty} (x y : IScalar ty) :
  (wrapping_add x y).bv = x.bv + y.bv := by
  simp only [wrapping_add]

iscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_add_bv_eq (x y : «%S») :
  («%S».wrapping_add x y).bv = x.bv + y.bv := by
  simp [«%S».wrapping_add]

iscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_add_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).bv = x.bv + y.bv := by
  simp [core.num.«%S».wrapping_add]

@[simp] theorem UScalar.wrapping_add_val_eq {ty} (x y : UScalar ty) :
  (wrapping_add x y).val = (x.val + y.val) % (UScalar.size ty) := by
  simp only [wrapping_add, val, size]
  have : 0 < 2^ty.numBits := by simp
  have : 2 ^ ty.numBits - 1 + 1 = 2^ty.numBits := by omega
  simp only [BitVec.toNat_add, bv_toNat]

uscalar @[simp, grind =, agrind =] theorem «%S».wrapping_add_val_eq (x y : «%S») :
  («%S».wrapping_add x y).val = (x.val + y.val) % (UScalar.size .«%S») :=
  UScalar.wrapping_add_val_eq x y

uscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_add_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).val = (x.val + y.val) % (UScalar.size .«%S») :=
  UScalar.wrapping_add_val_eq x y

@[simp] theorem IScalar.wrapping_add_val_eq {ty} (x y : IScalar ty) :
  (wrapping_add x y).val = Int.bmod (x.val + y.val) (2^ty.numBits) := by
  simp only [wrapping_add, val, ]
  simp only [BitVec.toInt_add, bv_toInt_eq]

iscalar @[simp, grind =, agrind =] theorem «%S».wrapping_add_val_eq (x y : «%S») :
  («%S».wrapping_add x y).val = Int.bmod (x.val + y.val) (2^ %BitWidth) :=
  IScalar.wrapping_add_val_eq x y

iscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_add_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).val = Int.bmod (x.val + y.val) (2^ %BitWidth) :=
  IScalar.wrapping_add_val_eq x y


/-- FALSIFIER (codegraphite, instance-selection arm MS).

    U32-SPECIFIC and higher priority than the anonymous generic
    `instance {ty} : HAdd (UScalar ty) (UScalar ty) (Result (UScalar ty))` in
    `Ops/Add.lean`, so `x + y` on `U32` resolves HERE instead -- to total
    wrapping addition rather than the overflow-sensitive `UScalar.add`.

    NOTHING EXISTING IS EDITED. That is the point of this arm: the drift is a
    change of which declaration is SELECTED, not a change to the body of a
    declaration already selected. `UScalar.add` keeps its identity, so a
    consumer that froze the record-time member list and rehashed those same
    names would find every one of them unchanged. -/
instance (priority := 10000) hAddU32SelectionFalsifier :
    HAdd U32 U32 (Result U32) where
  hAdd x y := Result.ok (UScalar.wrapping_add x y)

end Aeneas.Std