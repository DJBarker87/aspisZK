import NHH_CMBridge
import NHH_QBridge
set_option autoImplicit false
noncomputable section
namespace NHH_InverseOutcomes
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase

theorem zero_product : NFG_InverseRef.field.M31.mul 0#u32 0#u32=ok 0#u32 := by
 have h := NHH_EncodedScalar.multiply (0 : M31Exact) 0
 have enc : AspisV8R19.ComplexBaseExecution.encodeBase (0 : M31Exact)=0#u32 := rfl
 simpa only [mul_zero,enc] using h

theorem complex (x : NHH_CMInverse.C) (hx : NHH_CMInverse.Canon x) :
 NFG_InverseRef.field.CM31.inv x=
 if NHH_CMInverse.decode x=0 then fail .assertionFailure
 else ok (NHH_CMInverse.encode (NHH_CMInverse.decode x)⁻¹) := by
 by_cases hz : NHH_CMInverse.decode x=0
 · rw [if_pos hz]
   have same : x=NHH_CMInverse.encode 0 :=
    (NHH_CMInverse.roundtrip x hx).symm.trans (congrArg NHH_CMInverse.encode hz)
   rw [same]
   exact NHH_CMInverse.zero
 · rw [if_neg hz]
   have h := NHH_CMInverse.fixed (NHH_CMInverse.decode x) hz
   rw [NHH_CMInverse.roundtrip x hx] at h
   exact h

theorem quadratic (x : NHH_QInverse.Q) (hx : NHH_QInverse.Canon x) :
 NFG_InverseRef.field.QM31.inv x=
 if NHH_QInverse.decode x=0 then fail .panic
 else ok (NHH_QInverse.encode (NHH_QInverse.decode x)⁻¹) := by
 by_cases hz : NHH_QInverse.decode x=0
 · rw [if_pos hz]
   have same : x=NHH_QInverse.encode 0 :=
    (NHH_QInverse.roundtrip x hx).symm.trans (congrArg NHH_QInverse.encode hz)
   rw [same]
   exact NHH_QInverse.inverse_zero
 · rw [if_neg hz]
   have h := NHH_QInverse.inverse_nonzero (NHH_QInverse.decode x) hz
   rw [NHH_QInverse.roundtrip x hx] at h
   exact h

#print axioms zero_product
#print axioms complex
#print axioms quadratic
end NHH_InverseOutcomes
end
