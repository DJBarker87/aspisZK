import NLC_Rank
import NLC_LeafSound
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run erase)
/-- The progress fact is derived from actual source execution, rather than
supplied as a source endpoint or child-success premise. -/
theorem source_progress {H : Type} (s after : State H)
 (returned : (run (step s)).2 = ok (.inr after)) :
 rank after.next = rank s.next + 1 := by
 have actual : erase (step s) = ok (.inr after) := by
  rw [← PreparedHashCode.run_value]
  exact returned
 cases atSite : s.next with
 | rounds => exact all_erase (step s) (RankPost s) (rank_rounds s atSite) (.inr after) actual
 | mark2 => exact all_erase (step s) (RankPost s) (rank_mark2 s atSite) (.inr after) actual
 | claims => exact all_erase (step s) (RankPost s) (rank_claims s atSite) (.inr after) actual
 | original => exact all_erase (step s) (RankPost s) (rank_original s atSite) (.inr after) actual
 | terminal => exact all_erase (step s) (RankPost s) (rank_terminal s atSite) (.inr after) actual
 | mapPublic => exact all_erase (step s) (RankPost s) (rank_mapPublic s atSite) (.inr after) actual
 | mark3 => exact all_erase (step s) (RankPost s) (rank_mark3 s atSite) (.inr after) actual
 | lowArray => exact all_erase (step s) (RankPost s) (rank_lowArray s atSite) (.inr after) actual
 | highArray => exact all_erase (step s) (RankPost s) (rank_highArray s atSite) (.inr after) actual
 | blind => exact all_erase (step s) (RankPost s) (rank_blind s atSite) (.inr after) actual
 | alpha => exact all_erase (step s) (RankPost s) (rank_alpha s atSite) (.inr after) actual
 | mask => exact all_erase (step s) (RankPost s) (rank_mask s atSite) (.inr after) actual
 | record25a => exact all_erase (step s) (RankPost s) (rank_record25a s atSite) (.inr after) actual
 | decode25 => exact all_erase (step s) (RankPost s) (rank_decode25 s atSite) (.inr after) actual
 | multiply => exact all_erase (step s) (RankPost s) (rank_multiply s atSite) (.inr after) actual
 | addMask => exact all_erase (step s) (RankPost s) (rank_addMask s atSite) (.inr after) actual
 | extra28 => exact all_erase (step s) (RankPost s) (rank_extra28 s atSite) (.inr after) actual
 | addExtra => exact all_erase (step s) (RankPost s) (rank_addExtra s atSite) (.inr after) actual
 | terminalGuard => exact all_erase (step s) (RankPost s) (rank_terminalGuard s atSite) (.inr after) actual
 | mark4 => exact all_erase (step s) (RankPost s) (rank_mark4 s atSite) (.inr after) actual
 | stateBefore => exact all_erase (step s) (RankPost s) (rank_stateBefore s atSite) (.inr after) actual
 | record25b => exact all_erase (step s) (RankPost s) (rank_record25b s atSite) (.inr after) actual
 | circle0 => exact all_erase (step s) (RankPost s) (rank_circle0 s atSite) (.inr after) actual
 | record26a => exact all_erase (step s) (RankPost s) (rank_record26a s atSite) (.inr after) actual
 | decode26 => exact all_erase (step s) (RankPost s) (rank_decode26 s atSite) (.inr after) actual
 | record26b => exact all_erase (step s) (RankPost s) (rank_record26b s atSite) (.inr after) actual
 | circle1 => exact all_erase (step s) (RankPost s) (rank_circle1 s atSite) (.inr after) actual
 | mark5 => exact all_erase (step s) (RankPost s) (rank_mark5 s atSite) (.inr after) actual
 | circleGuard => exact all_erase (step s) (RankPost s) (rank_circleGuard s atSite) (.inr after) actual
 | payload2 => exact all_erase (step s) (RankPost s) (rank_payload2 s atSite) (.inr after) actual
 | rootCopy => exact all_erase (step s) (RankPost s) (rank_rootCopy s atSite) (.inr after) actual
 | verified => exact all_erase (step s) (RankPost s) (rank_verified s atSite) (.inr after) actual
 | lowIndex =>
   have impossible : (fail .panic : Result (Post H)) = ok (.inr after) := by
    simpa only [step,atSite] using actual
   cases impossible
 | highIndex =>
   have impossible : (fail .panic : Result (Post H)) = ok (.inr after) := by
    simpa only [step,atSite] using actual
   cases impossible

def fuel {H : Type} (s : State H) : Nat := 34 - rank s.next

theorem fuel_positive {H : Type} (s : State H) : 0 < fuel s := by
 have := rank_bound s.next
 unfold fuel
 omega

theorem fuel_next {H : Type} (s after : State H)
 (returned : (run (step s)).2 = ok (.inr after)) : fuel s = fuel after + 1 := by
 have order := source_progress s after returned
 have beforeBound := rank_bound s.next
 have afterBound := rank_bound after.next
 unfold fuel
 omega
#print axioms source_progress
#print axioms fuel_positive
#print axioms fuel_next
end AspisR1.NLC_Finish
end
