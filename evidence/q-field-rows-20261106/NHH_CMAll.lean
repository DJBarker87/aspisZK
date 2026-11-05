import NHH_AllScalar
import NHH_CMAlgebra
set_option autoImplicit false
noncomputable section
namespace NHH_CMAll
open Aeneas Aeneas.Std Result
open NHH_CMInverse (C toSampler)
abbrev SC := AspisR72Sampler.field.CM31
def fromSampler (x : SC) : C := ⟨x.a,x.b⟩

theorem from_to (x : C) : fromSampler (toSampler x)=x := by cases x;rfl
theorem to_from (x : SC) : toSampler (fromSampler x)=x := by cases x;rfl

theorem pullback (r : Result C) :
 r=(do let y ← (do let z ← r;ok (toSampler z));ok (fromSampler y)) := by
 cases r with
 | ok v => simp only [bind_tc_ok,from_to]
 | fail e => rfl
 | div => rfl

/-- Arbitrary callback Result, including failure/divergence, is preserved.
This is model-only; it supplies no generic function-pointer Kani credit. -/
theorem inv_with (x : C) (backend : U32 → Result U32) :
 (do let z ← NFG_InverseRef.field.CM31.inv_with x backend;ok (toSampler z))=
 AspisR72Sampler.field.CM31.inv_with (toSampler x) backend := by
 simp only [NFG_InverseRef.field.CM31.inv_with,AspisR72Sampler.field.CM31.inv_with,
  NHH_AllScalar.multiply,NHH_CMSampler.scalar_add,NHH_CMSampler.scalar_neg,
  toSampler,bind_assoc_eq,bind_tc_ok]

theorem inverse_association (x : C) :
 (do let z ← NFG_InverseRef.field.CM31.inv x;ok (toSampler z))=
 AspisR72Sampler.field.CM31.inv (toSampler x) := by
 simp only [NFG_InverseRef.field.CM31.inv,AspisR72Sampler.field.CM31.inv]
 rw [show NFG_InverseRef.field.M31.inv=AspisR72Sampler.field.M31.inv from funext NHH_AllScalar.inverse]
 exact inv_with x _

theorem mul_association (x y : C) :
 (do let z ← NFG_InverseRef.field.CM31.mul x y;ok (toSampler z))=
 AspisR72Sampler.field.CM31.mul (toSampler x) (toSampler y) := by
 simp only [NFG_InverseRef.field.CM31.mul,AspisR72Sampler.field.CM31.mul,
 NHH_AllScalar.multiply,NHH_CMSampler.scalar_sub,NHH_CMSampler.scalar_reduce,
 NHH_CMSampler.raw_product,toSampler,bind_assoc_eq,bind_tc_ok]

theorem square_association (x : C) :
 (do let z ← NFG_InverseRef.field.CM31.square x;ok (toSampler z))=
 AspisR72Sampler.field.CM31.square (toSampler x) := by
 simp only [NFG_InverseRef.field.CM31.square,AspisR72Sampler.field.CM31.square,
 NHH_AllScalar.multiply,NHH_CMSampler.scalar_double,NHH_CMSampler.scalar_reduce,
 NHH_CMSampler.raw_product,NFG_InverseRef.field.P,AspisR72Sampler.field.P,toSampler,bind_assoc_eq,bind_tc_ok]

theorem inverse_result (x : C) : NFG_InverseRef.field.CM31.inv x=
 (do let z ← AspisR72Sampler.field.CM31.inv (toSampler x);ok (fromSampler z)) := by
 rw [pullback (NFG_InverseRef.field.CM31.inv x),inverse_association]
theorem mul_result (x y : C) : NFG_InverseRef.field.CM31.mul x y=
 (do let z ← AspisR72Sampler.field.CM31.mul (toSampler x) (toSampler y);ok (fromSampler z)) := by
 rw [pullback (NFG_InverseRef.field.CM31.mul x y),mul_association]
theorem square_result (x : C) : NFG_InverseRef.field.CM31.square x=
 (do let z ← AspisR72Sampler.field.CM31.square (toSampler x);ok (fromSampler z)) := by
 rw [pullback (NFG_InverseRef.field.CM31.square x),square_association]
theorem sub_result (x y : C) : NFG_InverseRef.field.CM31.sub x y=
 (do let z ← AspisR72Sampler.field.CM31.sub (toSampler x) (toSampler y);ok (fromSampler z)) := by
 rw [pullback (NFG_InverseRef.field.CM31.sub x y),NHH_CMSampler.sub_association]
theorem neg_result (x : C) : NFG_InverseRef.field.CM31.neg x=
 (do let z ← AspisR72Sampler.field.CM31.neg (toSampler x);ok (fromSampler z)) := by
 rw [pullback (NFG_InverseRef.field.CM31.neg x),NHH_CMSampler.neg_association]
theorem rotate_result (x : C) : NFG_InverseRef.field.mul_by_r x=
 (do let z ← AspisR72Sampler.field.mul_by_r (toSampler x);ok (fromSampler z)) := by
 rw [pullback (NFG_InverseRef.field.mul_by_r x),NHH_CMSampler.rotate_association]

#print axioms from_to
#print axioms to_from
#print axioms pullback
#print axioms inv_with
#print axioms inverse_association
#print axioms mul_association
#print axioms square_association
#print axioms inverse_result
#print axioms mul_result
#print axioms square_result
#print axioms sub_result
#print axioms neg_result
#print axioms rotate_result
end NHH_CMAll
end
