import AspisR1SelectedMaskProbe.Funs
import NDH_Reference.Funs
set_option autoImplicit false
namespace NDH_Cmr
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

theorem add (a b : U32) :
    NDH_Reference.base_add_ref a b = field.M31.add a b := by
  simp only [NDH_Reference.base_add_ref, field.M31.add, field.P]

theorem sub (a b : U32) :
    NDH_Reference.base_sub_ref a b = field.M31.sub a b := by
  simp only [NDH_Reference.base_sub_ref, field.M31.sub, field.P]

theorem reference (a b : U32) :
    (do let (x,y) ← NDH_Reference.cmr_ref a b
        ok (field.CM31.mk x y)) = state_only_hiding.cm31_mul_r ⟨a,b⟩ := by
  simp only [NDH_Reference.cmr_ref, add, sub, state_only_hiding.cm31_mul_r,
    field.M31.double, field.CM31.new]

#print axioms add
#print axioms sub
#print axioms reference
end NDH_Cmr
