import NLM_TokenAcquire
set_option autoImplicit false
noncomputable section
namespace NLM_TokenRelease
open Aeneas Aeneas.Std NLM_Snapshot NLF_SdkModel
/-- The admitted release primitive runs on the SAME acquired guard/cell;
it restores all cells and records the SDK event after the earlier prefix. -/
theorem release (e : AspisR1.S2W_D189Entry.Entry) (t a : Nat)
 (owned : List NLM_Snapshot.Owned) (events : List NLF_ParentModel.Event) :
 NLF_ParentModel.release
  ⟨acquired (ready e t owned) a,t+1,events⟩ (guard (ready e t owned) a)=
 (⟨(ready e t owned).sdk,t+1,events++[.release (guard (ready e t owned) a) (.ok ())]⟩,.ok ()) := by
 unfold NLF_ParentModel.release
 rw [NLM_Snapshot.release_current]
#print release
#print axioms release
end NLM_TokenRelease
