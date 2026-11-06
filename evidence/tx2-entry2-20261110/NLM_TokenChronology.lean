import NLM_SevenTrace
import NLM_TokenEvents
set_option autoImplicit false
noncomputable section
namespace NLM_TokenChronology
open NLM_Snapshot NLM_SevenSnapshots AspisR1.S2W_D189Entry
/-- No deduplication when two account occurrences name the same admitted cell. -/
def tokens (e : Entry) : Nat → List NLM_Snapshot.Owned → List Site → List NLF_ParentModel.Event
 | _,_,[] => []
 | t,owned,c::cs =>
   [.acquire c.account t .shared (.ok (guard (ready e t owned) c.account)),
    .deref (guard (ready e t owned) c.account)
      (.ok (NLF_SdkModel.deref (acquired (ready e t owned) c.account) (guard (ready e t owned) c.account))),
    .release (guard (ready e t owned) c.account) (.ok ())] ++
   tokens e (t+1) (owned++[e.snapshot c.account c.lo c.hi]) cs

theorem projected (e : Entry) (t : Nat) (owned : List NLM_Snapshot.Owned) (cs : List Site) :
 (chronological e t owned cs).filterMap NLM_TokenEvents.sdk=tokens e t owned cs := by
 induction cs generalizing t owned with
 | nil => rfl
 | cons c cs ih =>
   simp only [chronological,List.filterMap_append,NLM_TokenEvents.normal,tokens,ih] <;> rfl
#print projected
#print axioms projected
end NLM_TokenChronology
