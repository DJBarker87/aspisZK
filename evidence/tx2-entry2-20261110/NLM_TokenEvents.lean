import NLM_SnapshotTrace
import NLF_ParentModel
set_option autoImplicit false
noncomputable section
namespace NLM_TokenEvents
open Aeneas Aeneas.Std Result NLM_Snapshot NLF_SdkModel
/-- Projection to the admitted SDK law's token events. Allocation and returned
owned values remain in the full parent log, not fabricated SDK actions. -/
def sdk : NLM_Snapshot.Event → Option NLF_ParentModel.Event
 | .acquire _ a t _ (.ok reply) => some (.acquire a t .shared reply)
 | .deref _ g (.ok payload) => some (.deref g (.ok payload))
 | .release _ g (.ok (.ok _)) => some (.release g (.ok ()))
 | .release _ g (.ok (.error err)) => some (.release g (.error err))
 | _ => none

theorem normal (s : NLM_Snapshot.State) (a lo hi : Nat) :
 (normalEvents s a lo hi).filterMap sdk=
 [.acquire a s.next .shared (.ok (guard s a)),
  .deref (guard s a) (.ok (deref (acquired s a) (guard s a))),
  .release (guard s a) (.ok ())] := by
 unfold normalEvents
 split <;> rfl

theorem abort_prefix (s : NLM_Snapshot.State) (a : Nat) (allocation : Result Unit) :
 (allocationPrefix s a allocation).filterMap sdk=
 [.acquire a s.next .shared (.ok (guard s a)),
  .deref (guard s a) (.ok (deref (acquired s a) (guard s a)))] := rfl
#print normal
#print abort_prefix
#print axioms normal
#print axioms abort_prefix
end NLM_TokenEvents
