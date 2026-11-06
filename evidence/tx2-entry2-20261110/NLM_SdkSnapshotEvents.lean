import NLM_TokenEvents
import NLF_SnapshotEvents
set_option autoImplicit false
noncomputable section
namespace NLM_SdkSnapshotEvents
open NLM_Snapshot AspisR1.S2W_D189Entry NLF_SdkModel
/-- The parent token projection equals the actual admitted SDK snapshot
schedule at the SAME State/account/token, rather than a parallel event list. -/
theorem source (e : Entry) (t a lo hi : Nat) (owned : List NLM_Snapshot.Owned) :
 (normalEvents (ready e t owned) a lo hi).filterMap NLM_TokenEvents.sdk=
 NLF_SnapshotEvents.events (ready e t owned).sdk a t := by
 rw [NLM_TokenEvents.normal]
 unfold NLF_SnapshotEvents.events
 have h := NLM_Snapshot.acquire e t a owned
 change try_borrow_data (ready e t owned).sdk a t=_ at h
 rw [h]
 simp [NLM_Snapshot.acquired,NLM_Snapshot.guard,NLF_SdkModel.deref,NLF_SdkModel.put,NLM_Snapshot.ready]
#print source
#print axioms source
end NLM_SdkSnapshotEvents
