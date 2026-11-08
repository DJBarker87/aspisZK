import NNR_C04Domain
set_option autoImplicit false
namespace AspisR1.NNR_ReturnedLog
open Aeneas Aeneas.Std Result NJU_CommonObserved
/-- A returned enclosing run cannot contain an outer-failing Merkle reply. -/
def Returned : Event → Prop
 | .merkle _ _ _ reply => ∃ u, reply = .ok u
 | _ => True
def Safe {A : Type} (m : NJU_Log.Run Event A) : Prop :=
 ∀ value, m.result = .ok value → NKE_EventAll.Holds Returned m

theorem bind_safe {A B : Type} (m : NJU_Log.Run Event A)
 (k : A → NJU_Log.Run Event B) (hm : Safe m) (hk : ∀ value, Safe (k value)) : Safe (m >>= k) := by
 cases m with
 | mk result events =>
  cases result with
  | fail e => intro value h; cases h
  | div => intro value h; cases h
  | ok a =>
   intro value h e member
   change e ∈ events ++ (k a).events at member
   rcases List.mem_append.mp member with left | right
   · exact hm a rfl e left
   · exact hk a value h e right

theorem lift_safe {A : Type} (m : Result A) : Safe (liftM m) := by
 intro value _ e member
 cases member

theorem pure_safe {A : Type} (value : A) : Safe (pure value : NJU_Log.Run Event A) := by
 intro _ _ e member
 cases member

theorem record_safe {A : Type} (event : Result A → Event) (call : Result A)
 (good : ∀ value, Returned (event (.ok value))) : Safe (NJU_Log.record event call) := by
 intro value returned e member
 change call = .ok value at returned
 rcases List.mem_singleton.mp member with rfl
 rw [returned]
 exact good value
#print axioms bind_safe
#print axioms lift_safe
#print axioms pure_safe
#print axioms record_safe
end AspisR1.NNR_ReturnedLog
