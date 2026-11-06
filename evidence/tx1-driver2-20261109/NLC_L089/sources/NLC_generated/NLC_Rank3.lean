import NLC_Step_decode26
import NLC_Step_record26b
import NLC_Step_circle1
import NLC_Step_mark5
import NLC_Step_circleGuard
import NLC_Step_payload2
import NLC_Step_rootCopy
import NLC_Step_verified
import NLC_RankBase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Every possible returning reply advances exactly one source state. -/
theorem rank_decode26 {H : Type} (s : State H) (atSite : s.next = .decode26) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_decode26 s atSite]
 unfold window_decode26
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_decode26

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_record26b {H : Type} (s : State H) (atSite : s.next = .record26b) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_record26b s atSite]
 unfold window_record26b
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_record26b

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_circle1 {H : Type} (s : State H) (atSite : s.next = .circle1) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_circle1 s atSite]
 unfold window_circle1
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_circle1

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_mark5 {H : Type} (s : State H) (atSite : s.next = .mark5) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_mark5 s atSite]
 unfold window_mark5
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_mark5

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_circleGuard {H : Type} (s : State H) (atSite : s.next = .circleGuard) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_circleGuard s atSite]
 unfold window_circleGuard
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_circleGuard

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_payload2 {H : Type} (s : State H) (atSite : s.next = .payload2) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_payload2 s atSite]
 unfold window_payload2
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_payload2

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_rootCopy {H : Type} (s : State H) (atSite : s.next = .rootCopy) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_rootCopy s atSite]
 unfold window_rootCopy
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_rootCopy

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_verified {H : Type} (s : State H) (atSite : s.next = .verified) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_verified s atSite]
 unfold window_verified
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_verified

end AspisR1.NLC_Finish
end
