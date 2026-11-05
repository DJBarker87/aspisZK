import NGM_DoubleRef.Funs
import NGM_ResultLaws
import NGM_ScalarCanon
import AspisR1SelectedMaskProbe.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGM_AddReference
open AspisR1SelectedMaskProbe

theorem add_reference (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
 NGM_DoubleRef.add_ref x y=field.M31.add x y := by
 unfold NGM_DoubleRef.add_ref field.M31.add field.P
 rw [NGM_ScalarCanon.checked_add x y (by omega)]
 simp only [lift,bind_tc_ok]
 split
 · rw [NGM_ScalarCanon.checked_sub (U32.wrapping_add x y) 2147483647#u32 (by scalar_tac)]
 · rfl
#print axioms add_reference
end NGM_AddReference
