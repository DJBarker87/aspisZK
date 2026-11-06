import NKE_EventAll
set_option autoImplicit false
namespace NKE_Entered
open Aeneas Aeneas.Std Result
/-- Retain the actual Result equation when entering a continuation. This is
an internal bind inversion, never a new positive-root hypothesis. -/
theorem bind_all {E A B : Type} (P : E → Prop) (m : NJU_Log.Run E A)
 (k : A → NJU_Log.Run E B) (before : NKE_EventAll.Holds P m)
 (after : ∀ value,m.result=.ok value → NKE_EventAll.Holds P (k value)) :
 NKE_EventAll.Holds P (m >>= k) := by
 cases m with
 | mk result events =>
  cases result with
  | fail err => exact before
  | div => exact before
  | ok value =>
   intro event member
   change event∈events++(k value).events at member
   rcases List.mem_append.mp member with first|last
   · exact before event first
   · exact after value rfl event last

theorem lift_ok {E A B : Type} (value : A) (k : A → NJU_Log.Run E B) :
 ((liftM (ok value) : NJU_Log.Run E A) >>= k)=k value := rfl
#print axioms bind_all
#print axioms lift_ok
end NKE_Entered
