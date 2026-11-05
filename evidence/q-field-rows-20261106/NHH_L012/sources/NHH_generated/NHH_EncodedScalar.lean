import NHH_ScalarDomain
import AspisV8R19.SamplerClosureCircleFieldExecution
set_option autoImplicit false
noncomputable section
namespace NHH_EncodedScalar
open Aeneas Aeneas.Std Result AspisR1
open AspisV8R19 AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase encodeBase_val)

theorem multiply (x y : M31Exact) :
 NFG_InverseRef.field.M31.mul (encodeBase x) (encodeBase y)=ok (encodeBase (x*y)) := by
 obtain ⟨out,ho,hv,hc⟩ := NHH_BaseOps.mul_value (encodeBase x) (encodeBase y)
 have same : out=encodeBase (x*y) := by
  apply UScalar.eq_of_val_eq
  simpa only [encodeBase_val,ZMod.val_mul] using hv
 exact same ▸ ho

theorem addition (x y : M31Exact) :
 NFG_InverseRef.field.M31.add (encodeBase x) (encodeBase y)=ok (encodeBase (x+y)) := by
 have primitive (a b : U32) : NFG_InverseRef.field.M31.add a b=AspisR72Sampler.field.M31.add a b := by
  simp only [NFG_InverseRef.field.M31.add,AspisR72Sampler.field.M31.add,
  NFG_InverseRef.field.P,AspisR72Sampler.field.P]
 exact (primitive _ _).trans (SamplerClosureCircleScalarTransport.add_encode x y)

theorem negation (x : M31Exact) :
 NFG_InverseRef.field.M31.neg (encodeBase x)=ok (encodeBase (-x)) := by
 have primitive (a : U32) : NFG_InverseRef.field.M31.neg a=AspisR72Sampler.field.M31.neg a := by
  simp only [NFG_InverseRef.field.M31.neg,AspisR72Sampler.field.M31.neg,
  NFG_InverseRef.field.P,AspisR72Sampler.field.P]
 exact (primitive _).trans (SamplerClosureCircleScalarTransport.neg_encode x)

theorem inverse (x : M31Exact) (hx : x≠0) :
 NFG_InverseRef.field.M31.inv (encodeBase x)=ok (encodeBase x⁻¹) := by
 have dec : R17CurrentM31Semantics.decode (encodeBase x)=x := by
  simp only [R17CurrentM31Semantics.decode,encodeBase_val,ZMod.natCast_zmod_val]
 obtain ⟨out,ho,hv⟩ := AspisR1M31Inverse.SquareProof.current_inv_total_inverse (encodeBase x) (by rw [dec];exact hx)
 have hc := AspisR1M31Inverse.SquareProof.current_inv_success_canonical (encodeBase x) out ho
 have same : out=encodeBase x⁻¹ := by
  apply UScalar.eq_of_val_eq
  have vals := congrArg ZMod.val hv
  simpa only [R17CurrentM31Semantics.decode,encodeBase_val,ZMod.val_natCast_of_lt hc,dec] using vals
 exact (NHH_ScalarDomain.inverse_probe _).trans (same ▸ ho)

#print axioms multiply
#print axioms addition
#print axioms negation
#print axioms inverse
end NHH_EncodedScalar
end
