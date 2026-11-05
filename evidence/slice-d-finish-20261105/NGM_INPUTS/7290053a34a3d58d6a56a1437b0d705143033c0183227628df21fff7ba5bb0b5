import NGM_DoubleRef.Funs
import NGM_ResultLaws
import AspisR1SelectedMaskProbe.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGM_AddReference
open AspisR1SelectedMaskProbe

theorem add_reference (x y : U32) :
    NGM_DoubleRef.add_ref x y = field.M31.add x y := by
  simp [NGM_DoubleRef.add_ref,field.M31.add,field.P]

#print axioms add_reference
end NGM_AddReference
