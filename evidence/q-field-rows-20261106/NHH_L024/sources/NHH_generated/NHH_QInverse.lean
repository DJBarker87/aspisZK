import NHH_CMAlgebra
import NHH_CMBridge
set_option autoImplicit false
noncomputable section
namespace NHH_QInverse
open Aeneas Aeneas.Std Result
open AspisV8R19 AspisV8R15.ExactTowerBase
abbrev Q := NFG_InverseRef.field.QM31

def encode (x : QM31Exact) : Q := ⟨NHH_CMInverse.encode x.re,NHH_CMInverse.encode x.im⟩
def toSampler (x : Q) : AspisR72Sampler.field.QM31 :=
 ⟨NHH_CMInverse.toSampler x.c0,NHH_CMInverse.toSampler x.c1⟩
def decode (x : Q) : QM31Exact := ⟨NHH_CMInverse.decode x.c0,NHH_CMInverse.decode x.c1⟩
def Canon (x : Q) : Prop := NHH_CMInverse.Canon x.c0 ∧ NHH_CMInverse.Canon x.c1

theorem roundtrip (x : Q) (hx : Canon x) : encode (decode x)=x := by
 rcases x with ⟨a,b⟩
 exact congrArg₂ NFG_InverseRef.field.QM31.mk (NHH_CMInverse.roundtrip a hx.1) (NHH_CMInverse.roundtrip b hx.2)

theorem canonical (x : QM31Exact) : Canon (encode x) :=
 ⟨NHH_CMBridge.encoded_canonical x.re,NHH_CMBridge.encoded_canonical x.im⟩

theorem test_association (x : Q) :
 NFG_InverseRef.field.QM31.is_zero x=AspisR72Sampler.field.QM31.is_zero (toSampler x) := by
 simp only [NFG_InverseRef.field.QM31.is_zero,NFG_InverseRef.field.CM31.is_zero,
 NFG_InverseRef.field.M31.is_zero,AspisR72Sampler.field.QM31.is_zero,
 AspisR72Sampler.field.CM31.is_zero,AspisR72Sampler.field.M31.is_zero,
 toSampler,NHH_CMInverse.toSampler,bind_tc_ok]

theorem zero_test (x : QM31Exact) :
 NFG_InverseRef.field.QM31.is_zero (encode x)=ok (decide (x=0)) :=
 (test_association _).trans (SamplerClosureCircleFieldExecution.zero_test x)

theorem try_nonzero (x : QM31Exact) (hx : x≠0) :
 NFG_InverseRef.field.QM31.try_inv (encode x)=ok (some (encode x⁻¹)) := by
 have hn := NormInverse.quartic_norm_nonzero x hx
 have hi := NHH_CMInverse.fixed (NormInverse.quarticNorm x) hn
 have he : (⟨x.re*(NormInverse.quarticNorm x)⁻¹,
  (-x.im)*(NormInverse.quarticNorm x)⁻¹⟩ : QM31Exact)=x⁻¹ := by
  rw [←NormInverse.quartic_inverse_correct x hx]
  simp only [NormInverse.quarticInverse,NormInverse.complex_inverse_correct _ hn]
 simp only [NormInverse.quarticNorm] at hi
 calc
  NFG_InverseRef.field.QM31.try_inv (encode x)=ok (some (encode
   (⟨x.re*(NormInverse.quarticNorm x)⁻¹,(-x.im)*(NormInverse.quarticNorm x)⁻¹⟩ : QM31Exact))) := by
   simp only [NFG_InverseRef.field.QM31.try_inv,zero_test,hx,decide_false,bind_tc_ok,Bool.false_eq_true,if_false]
   simp only [encode,NormInverse.quarticNorm,NHH_CMAlgebra.square,NHH_CMAlgebra.rotate,
    NHH_CMAlgebra.subtraction,hi,NHH_CMAlgebra.multiply,NHH_CMAlgebra.negation,bind_tc_ok]
  _=ok (some (encode x⁻¹)) := by rw [he]

theorem try_zero : NFG_InverseRef.field.QM31.try_inv (encode 0)=ok none := by
 simp only [NFG_InverseRef.field.QM31.try_inv,zero_test,decide_true,bind_tc_ok,Bool.true_eq_true,if_true]

theorem inverse_nonzero (x : QM31Exact) (hx : x≠0) :
 NFG_InverseRef.field.QM31.inv (encode x)=ok (encode x⁻¹) := by
 rw [NFG_InverseRef.field.QM31.inv,try_nonzero x hx];rfl

theorem inverse_zero : NFG_InverseRef.field.QM31.inv (encode 0)=fail .panic := by
 rw [NFG_InverseRef.field.QM31.inv,try_zero];rfl

theorem try_association (x : QM31Exact) :
 (do let out ← NFG_InverseRef.field.QM31.try_inv (encode x)
     ok (out.map toSampler))=
 AspisR72Sampler.field.QM31.try_inv (SamplerClosureProductExecution.encode x) := by
 by_cases hx : x=0
 · subst x
   rw [try_zero,SamplerClosureCircleFieldExecution.try_inverse_zero];rfl
 · rw [try_nonzero x hx,SamplerClosureCircleFieldExecution.try_inverse_nonzero x hx];rfl

theorem canonical_try_association (x : Q) (hx : Canon x) :
 (do let out ← NFG_InverseRef.field.QM31.try_inv x;ok (out.map toSampler))=
 AspisR72Sampler.field.QM31.try_inv (toSampler x) := by
 have h := try_association (decode x)
 rw [roundtrip x hx] at h
 have raw : SamplerClosureProductExecution.encode (decode x)=toSampler x := congrArg toSampler (roundtrip x hx)
 rw [raw] at h
 exact h

#print axioms roundtrip
#print axioms canonical
#print axioms test_association
#print axioms zero_test
#print axioms try_nonzero
#print axioms try_zero
#print axioms inverse_nonzero
#print axioms inverse_zero
#print axioms try_association
#print axioms canonical_try_association
end NHH_QInverse
end
