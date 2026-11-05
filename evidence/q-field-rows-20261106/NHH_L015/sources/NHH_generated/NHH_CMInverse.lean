import NHH_EncodedScalar
set_option autoImplicit false
noncomputable section
namespace NHH_CMInverse
open Aeneas Aeneas.Std Result
open AspisV8R19 AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase)
abbrev C := NFG_InverseRef.field.CM31

def encode (x : CM31Exact) : C := ⟨encodeBase x.re,encodeBase x.im⟩
def toSampler (x : C) : AspisR72Sampler.field.CM31 := ⟨x.a,x.b⟩
def decode (x : C) : CM31Exact := ⟨(x.a.val : M31Exact),(x.b.val : M31Exact)⟩
def Canon (x : C) : Prop := x.a.val<2147483647 ∧ x.b.val<2147483647

theorem roundtrip (x : C) (hx : Canon x) : encode (decode x)=x := by
 rcases x with ⟨a,b⟩
 have ha : encodeBase (a.val : M31Exact)=a := by
  apply UScalar.eq_of_val_eq
  simp only [ComplexBaseExecution.encodeBase_val,ZMod.val_natCast_of_lt hx.1]
 have hb : encodeBase (b.val : M31Exact)=b := by
  apply UScalar.eq_of_val_eq
  simp only [ComplexBaseExecution.encodeBase_val,ZMod.val_natCast_of_lt hx.2]
 exact congrArg₂ NFG_InverseRef.field.CM31.mk ha hb

theorem fixed (x : CM31Exact) (hx : x≠0) :
 NFG_InverseRef.field.CM31.inv (encode x)=ok (encode x⁻¹) := by
 have hn := NormInverse.complex_norm_nonzero x hx
 have hbase := NHH_EncodedScalar.inverse (NormInverse.complexNorm x) hn
 have he : (⟨x.re*(NormInverse.complexNorm x)⁻¹,
  (-x.im)*(NormInverse.complexNorm x)⁻¹⟩ : CM31Exact)=x⁻¹ := by
  rw [←NormInverse.complex_inverse_correct x hx]
  simp only [NormInverse.complexInverse,NormInverse.base_inverse_correct _ hn]
 simp only [NormInverse.complexNorm] at hbase
 calc
  NFG_InverseRef.field.CM31.inv (encode x)=ok (encode
   (⟨x.re*(NormInverse.complexNorm x)⁻¹,(-x.im)*(NormInverse.complexNorm x)⁻¹⟩ : CM31Exact)) := by
   simp only [NFG_InverseRef.field.CM31.inv,NFG_InverseRef.field.CM31.inv_with,
    encode,NormInverse.complexNorm,NHH_EncodedScalar.multiply,NHH_EncodedScalar.addition,
    hbase,NHH_EncodedScalar.negation,bind_tc_ok]
  _=ok (encode x⁻¹) := by rw [he]

theorem zero : NFG_InverseRef.field.CM31.inv (encode 0)=fail .assertionFailure := by
 simp only [NFG_InverseRef.field.CM31.inv,NFG_InverseRef.field.CM31.inv_with,
  encode,QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero,NHH_EncodedScalar.multiply,
  NHH_EncodedScalar.addition,mul_zero,add_zero,bind_tc_ok]
 change (do let z ← NFG_InverseRef.field.M31.inv 0#u32; _)=_
 rw [NHH_ScalarDomain.inverse_zero];rfl

theorem encoded_association (x : CM31Exact) (hx : x≠0) :
 (do let out ← NFG_InverseRef.field.CM31.inv (encode x);ok (toSampler out))=
 AspisR72Sampler.field.CM31.inv (SamplerClosureProductExecution.encodeCM x) := by
 rw [fixed x hx,SamplerClosureCircleFieldExecution.cm_inv x hx]
 rfl

/-- Same canonical receiver in the frozen body and adopted cohort, with zero's
assertion terminal retained separately. -/
theorem canonical_association (x : C) (hx : Canon x) (live : decode x≠0) :
 (do let out ← NFG_InverseRef.field.CM31.inv x;ok (toSampler out))=
 AspisR72Sampler.field.CM31.inv (toSampler x) := by
 have h := encoded_association (decode x) live
 rw [roundtrip x hx] at h
 have raw : SamplerClosureProductExecution.encodeCM (decode x)=toSampler x :=
  congrArg toSampler (roundtrip x hx)
 rw [raw] at h
 exact h

#print axioms roundtrip
#print axioms fixed
#print axioms zero
#print axioms encoded_association
#print axioms canonical_association
end NHH_CMInverse
end
