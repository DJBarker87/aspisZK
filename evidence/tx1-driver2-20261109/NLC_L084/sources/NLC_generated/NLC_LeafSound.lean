import NLC_FrameAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code erase run)
/-- Arbitrary-reply frame laws imply the property of every actual returning
source execution, without assuming that a child succeeds. -/
theorem all_erase {A : Type} (code : Code A) (P : A → Prop) (leaves : AllLeaves P code)
 (a : A) (value : erase code = ok a) : P a := by
 induction code with
 | done b => cases value;exact leaves
 | step reply next ih =>
   cases reply with
   | ok b => exact ih b (leaves b) value
   | fail error => cases value
   | div => cases value
 | digest D hash parts next ih =>
   cases reply : D.digest hash parts with
   | ok b =>
     simp only [erase,reply,bind_tc_ok] at value
     exact ih b (leaves b) value
   | fail error => simp only [erase,reply,bind_tc_fail] at value;cases value
   | div => simp only [erase,reply,bind_tc_div] at value;cases value
#print axioms all_erase
end AspisR1.NLC_Finish
end
