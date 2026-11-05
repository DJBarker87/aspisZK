import NHH_CMAll
import NHH_QInverse
set_option autoImplicit false
noncomputable section
namespace NHH_QAll
open Aeneas Aeneas.Std Result
open NHH_QInverse (Q toSampler)

def fromSampler (x : AspisR72Sampler.field.QM31) : Q :=
 ⟨NHH_CMAll.fromSampler x.c0,NHH_CMAll.fromSampler x.c1⟩
theorem from_to (x : Q) : fromSampler (toSampler x)=x := by cases x; rfl
theorem to_from (x : AspisR72Sampler.field.QM31) : toSampler (fromSampler x)=x := by cases x;rfl

/-- Full all-raw partial Result: None, errors and divergence are transported,
without assuming success of any square, inverse or product. -/
theorem try_association (x : Q) :
 (do let o ← NFG_InverseRef.field.QM31.try_inv x;ok (o.map toSampler))=
 AspisR72Sampler.field.QM31.try_inv (toSampler x) := by
 simp only [NFG_InverseRef.field.QM31.try_inv,AspisR72Sampler.field.QM31.try_inv,
  NHH_QInverse.test_association,NHH_CMAll.square_result,NHH_CMAll.rotate_result,
  NHH_CMAll.sub_result,NHH_CMAll.inverse_result,NHH_CMAll.mul_result,
  NHH_CMAll.neg_result,bind_assoc_eq,bind_tc_ok,NHH_CMAll.to_from,
  toSampler,NHH_QInverse.toSampler,NHH_CMAll.fromSampler,NHH_CMInverse.toSampler,
  Option.map_some,Option.map_none] <;> rfl

theorem try_result (x : Q) : NFG_InverseRef.field.QM31.try_inv x=
 (do let o ← AspisR72Sampler.field.QM31.try_inv (toSampler x);ok (o.map fromSampler)) := by
 rw [←try_association]
 cases h : NFG_InverseRef.field.QM31.try_inv x with
 | ok o => cases o <;> simp only [bind_tc_ok,Option.map_none,Option.map_some,from_to]
 | fail e => rfl
 | div => rfl

/-- The exact source expect terminal on the SAME child Option. No new cohort
inverse stand-in and no successful-child premise is introduced. -/
theorem inverse_association (x : Q) :
 (do let out ← NFG_InverseRef.field.QM31.inv x;ok (toSampler out))=
 (do let o ← AspisR72Sampler.field.QM31.try_inv (toSampler x)
     core.option.Option.expect o NFG_PanicMessage.value) := by
 rw [NFG_InverseRef.field.QM31.inv,try_result]
 simp only [bind_assoc_eq,bind_tc_ok]
 congr 1
 funext o
 cases o <;> rfl

#print axioms from_to
#print axioms to_from
#print axioms try_association
#print axioms try_result
#print axioms inverse_association
end NHH_QAll
end
