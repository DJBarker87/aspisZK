import NLC_Step_rounds
import NLC_Step_mark2
import NLC_Step_claims
import NLC_Step_original
import NLC_Step_terminal
import NLC_Step_mapPublic
import NLC_Step_mark3
import NLC_Step_lowArray
import NLC_RankBase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Every possible returning reply advances exactly one source state. -/
theorem rank_rounds {H : Type} (s : State H) (atSite : s.next = .rounds) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_rounds s atSite]
 unfold window_rounds
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_rounds

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_mark2 {H : Type} (s : State H) (atSite : s.next = .mark2) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_mark2 s atSite]
 unfold window_mark2
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_mark2

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_claims {H : Type} (s : State H) (atSite : s.next = .claims) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_claims s atSite]
 unfold window_claims
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_claims

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_original {H : Type} (s : State H) (atSite : s.next = .original) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_original s atSite]
 unfold window_original
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_original

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_terminal {H : Type} (s : State H) (atSite : s.next = .terminal) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_terminal s atSite]
 unfold window_terminal
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_terminal

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_mapPublic {H : Type} (s : State H) (atSite : s.next = .mapPublic) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_mapPublic s atSite]
 unfold window_mapPublic
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_mapPublic

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_mark3 {H : Type} (s : State H) (atSite : s.next = .mark3) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_mark3 s atSite]
 unfold window_mark3
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_mark3

/-- Every possible returning reply advances exactly one source state. -/
theorem rank_lowArray {H : Type} (s : State H) (atSite : s.next = .lowArray) :
 AllLeaves (RankPost s) (step s) := by
 rw [step_lowArray s atSite]
 unfold window_lowArray
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply rank_returned; rw [atSite]; rfl)
 | (apply rank_put; rw [atSite]; rfl)
 | (apply rank_next; rw [atSite]; rfl)
 | (change True; trivial)
 | split
#print axioms rank_lowArray

end AspisR1.NLC_Finish
end
