import PV_L1D_CallbackSafe
set_option autoImplicit false
namespace PV_L1E_SafeObserve
open Aeneas Aeneas.Std
open PV_L1D_Logged PV_L1D_CallbackSafe
open R1Z.SideChannelL1AttemptRecord

theorem query {A : Type} (k : Nat) (r : Result A) :
    Safe (observe .queryScan k r) := safe_observe .queryScan k r (by rfl)
#print axioms query

theorem phase {A : Type} (site : Call) (k : Nat) (r : Result A)
    (notCallback : site ≠ .callback) : Safe (observe site k r) := by
  apply safe_observe
  cases site <;> simp only [callbacks,List.filterMap_cons,List.filterMap_nil]
  · exact (notCallback rfl).elim
  all_goals rfl
#print axioms phase
end PV_L1E_SafeObserve
