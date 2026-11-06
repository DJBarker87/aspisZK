import NLC_Step_extra28
import NLC_Step_addExtra
import NLC_Step_terminalGuard
import NLC_Step_mark4
import NLC_Step_stateBefore
import NLC_Step_record25b
import NLC_Step_circle0
import NLC_Step_record26a
import NLC_RankBase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Every possible returning reply advances exactly one source state. -/
theorem rank_extra28 {H : Type} (s : State H) (atSite : s.next = .extra28) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_extra28 s atSite]
 unfold window_extra28
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_extra28

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_addExtra {H : Type} (s : State H) (atSite : s.next = .addExtra) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_addExtra s atSite]
 unfold window_addExtra
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_addExtra

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_terminalGuard {H : Type} (s : State H) (atSite : s.next = .terminalGuard) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_terminalGuard s atSite]
 unfold window_terminalGuard
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_terminalGuard

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_mark4 {H : Type} (s : State H) (atSite : s.next = .mark4) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_mark4 s atSite]
 unfold window_mark4
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_mark4

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_stateBefore {H : Type} (s : State H) (atSite : s.next = .stateBefore) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_stateBefore s atSite]
 unfold window_stateBefore
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_stateBefore

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_record25b {H : Type} (s : State H) (atSite : s.next = .record25b) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_record25b s atSite]
 unfold window_record25b
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_record25b

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_circle0 {H : Type} (s : State H) (atSite : s.next = .circle0) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_circle0 s atSite]
 unfold window_circle0
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_circle0

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_record26a {H : Type} (s : State H) (atSite : s.next = .record26a) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_record26a s atSite]
 unfold window_record26a
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_record26a

end AspisR1.NLC_Finish
end
