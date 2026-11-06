import NLM_TokenChronology
import NLM_SevenSites
set_option autoImplicit false
noncomputable section
namespace NLM_TokenCounts
open NLM_Snapshot NLM_SevenSnapshots AspisR1.S2W_D189Entry
/-- Counts occurrences, not distinct cell addresses. -/
theorem count (e : Entry) (t : Nat) (owned : List NLM_Snapshot.Owned) (cs : List Site) :
 (NLM_TokenChronology.tokens e t owned cs).length=3*cs.length := by
 induction cs generalizing t owned with
 | nil => rfl
 | cons c cs ih => simp [NLM_TokenChronology.tokens,ih] <;> omega

theorem seven (e : Entry) :
 ((chronological e 0 [] NLM_SevenSites.sites).filterMap NLM_TokenEvents.sdk).length=21 := by
 rw [NLM_TokenChronology.projected,count]
 rfl
#print count
#print seven
#print axioms count
#print axioms seven
end NLM_TokenCounts
