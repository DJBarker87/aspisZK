import NJU_Log
set_option autoImplicit false
namespace NKE_EventAll
open Aeneas Aeneas.Std
/-- Logical clauses of the actual source log, not independent endpoint inputs. -/
def Holds {E A : Type} (P : E → Prop) (m : NJU_Log.Run E A) : Prop :=
 ∀ e∈m.events,P e

theorem bind_all {E A B : Type} (P : E → Prop) (m : NJU_Log.Run E A)
 (k : A → NJU_Log.Run E B) (hm : Holds P m) (hk : ∀ value,Holds P (k value)) :
 Holds P (m >>= k) := by
 cases m with
 | mk result events =>
  cases result with
  | fail e => exact hm
  | div => exact hm
  | ok value =>
   intro e member
   change e∈events ++ (k value).events at member
   rcases List.mem_append.mp member with left|right
   · exact hm e left
   · exact hk value e right

theorem lift_all {E A : Type} (P : E → Prop) (m : Result A) :
 Holds P (liftM m) := by intro e member;cases member

theorem pure_all {E A : Type} (P : E → Prop) (value : A) :
 Holds P (pure value : NJU_Log.Run E A) := by intro e member;cases member

theorem record_all {E A : Type} (P : E → Prop) (event : Result A → E)
 (call : Result A) (law : P (event call)) : Holds P (NJU_Log.record event call) := by
 intro e member
 rcases List.mem_singleton.mp member with rfl
 exact law
#print axioms bind_all
#print axioms lift_all
#print axioms pure_all
#print axioms record_all
end NKE_EventAll
