import NFG_CheckedFieldRef.Funs
import AspisR72Sampler.Funs
import NFG_ResultCongr
set_option autoImplicit false
namespace NFG_NegAssociation
open Aeneas Aeneas.Std Result
def cm (x : NFG_CheckedFieldRef.field.CM31) : AspisR72Sampler.field.CM31 := ⟨x.a,x.b⟩
/-- Exact partial Result, including every subtraction error; no canonicality premise. -/
theorem primitive (x : U32) : NFG_CheckedFieldRef.field.M31.neg x =
 AspisR72Sampler.field.M31.neg x := by
 simp only [NFG_CheckedFieldRef.field.M31.neg,AspisR72Sampler.field.M31.neg,
  NFG_CheckedFieldRef.field.P,AspisR72Sampler.field.P]

theorem result (x : NFG_CheckedFieldRef.field.CM31) :
 (do let y ← NFG_CheckedFieldRef.field.CM31.neg x; ok (cm y)) =
 AspisR72Sampler.field.CM31.neg (cm x) := by
 simp only [NFG_CheckedFieldRef.field.CM31.neg,AspisR72Sampler.field.CM31.neg,
  cm,primitive,bind_assoc_eq,bind_tc_ok]
#print axioms primitive
#print axioms result
end NFG_NegAssociation
