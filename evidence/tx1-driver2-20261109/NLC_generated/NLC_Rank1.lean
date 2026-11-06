import NLC_Step_highArray
import NLC_Step_blind
import NLC_Step_alpha
import NLC_Step_mask
import NLC_Step_record25a
import NLC_Step_decode25
import NLC_Step_multiply
import NLC_Step_addMask
import NLC_RankBase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Every possible returning reply advances exactly one source state. -/
theorem rank_highArray {H : Type} (s : State H) (atSite : s.next = .highArray) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_highArray s atSite]
 unfold window_highArray
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_highArray

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_blind {H : Type} (s : State H) (atSite : s.next = .blind) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_blind s atSite]
 unfold window_blind
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_blind

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_alpha {H : Type} (s : State H) (atSite : s.next = .alpha) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_alpha s atSite]
 unfold window_alpha
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_alpha

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_mask {H : Type} (s : State H) (atSite : s.next = .mask) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_mask s atSite]
 unfold window_mask
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_mask

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_record25a {H : Type} (s : State H) (atSite : s.next = .record25a) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_record25a s atSite]
 unfold window_record25a
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_record25a

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_decode25 {H : Type} (s : State H) (atSite : s.next = .decode25) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_decode25 s atSite]
 unfold window_decode25
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_decode25

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_multiply {H : Type} (s : State H) (atSite : s.next = .multiply) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_multiply s atSite]
 unfold window_multiply
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_multiply

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_addMask {H : Type} (s : State H) (atSite : s.next = .addMask) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_addMask s atSite]
 unfold window_addMask
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_addMask

end AspisR1.NLC_Finish
end
