import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Wrapping Add
-/

def UScalar.wrapping_add {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.bv + y.bv ⟩

/- CGR-M2 LIBRARY-ONLY C3 -- THE PRECISION CONTROL. NOT AN UPSTREAM CHANGE.

   A real change to the model library that is OUTSIDE the measured subject's
   closure. `panic_add_one` consumes the panicking add path (`UScalar.add`,
   `tryMk`, `Result.ofOption`); nothing reaches this declaration.

   An ADDED declaration rather than a mutated one, for a measured reason: every
   arithmetic definition in this library carries spec lemmas that state its
   denotation, so changing one falsifies its own specs and the library stops
   building. Measured twice -- on `UScalar.add`, where the falsifier had to admit
   three specs, and on `wrapping_add`, where two more broke. That self-checking
   property is defence in depth, and it also makes mutating an unused
   declaration in place surprisingly hard.

   Still a genuine library change in the EXECUTION environment: the declaration
   is elaborated and present, which the harness asserts POSITIVELY before
   trusting the precision result. Without that assertion an inactive mutation
   would masquerade as perfect precision. -/
def UScalar.cgr_m2_c3_unused_marker {ty} (x : UScalar ty) : UScalar ty := ⟨ x.bv ⟩

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

end Aeneas.Std
