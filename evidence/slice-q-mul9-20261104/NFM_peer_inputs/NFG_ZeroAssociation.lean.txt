import NFG_FieldRef.Funs
import AspisR72Sampler.Funs
set_option autoImplicit false
namespace NFG_ZeroAssociation
open Aeneas Aeneas.Std Result
def cm (x : NFG_FieldRef.field.CM31) : AspisR72Sampler.field.CM31 := ⟨x.a,x.b⟩
def qm (x : NFG_FieldRef.field.QM31) : AspisR72Sampler.field.QM31 := ⟨cm x.c0,cm x.c1⟩
/-- Complete all-raw Result and native short-circuit association; no success premise. -/
theorem result (x : NFG_FieldRef.field.QM31) :
 NFG_FieldRef.field.QM31.is_zero x = AspisR72Sampler.field.QM31.is_zero (qm x) := rfl
#print axioms result
end NFG_ZeroAssociation
