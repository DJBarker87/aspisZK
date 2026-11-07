import NLU_Invariant
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Code
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code erase)
/-- Preserve the actual child's full Result while passing its returned value
into the ONE parent continuation; fail/div have no suffix. -/
theorem erase_bind {A B : Type} (code : Code A) (next : A → Code B) :
 erase (PreparedHashCode.bind code next)=(do let value ← erase code;erase (next value)) := by
 induction code with
 | done value=>rfl
 | step reply tail ih=>
   cases reply with
   | fail error=>rfl
   | div=>rfl
   | ok value=>exact ih value
 | digest D hash parts tail ih=>
   simp only [PreparedHashCode.bind,erase]
   cases h : D.digest hash parts with
   | fail error=>simp only [h,bind_tc_fail]
   | div=>simp only [h,bind_tc_div]
   | ok value=>simpa only [h,bind_tc_ok] using ih value
#print axioms erase_bind
end AspisR1.NMC_Code
end
