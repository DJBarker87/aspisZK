import NLM_SevenSplit
set_option autoImplicit false
noncomputable section
namespace NLM_SevenAbort
open Aeneas Aeneas.Std NLM_Snapshot NLM_SevenSnapshots
theorem failed (allocation : Site → Result Unit) (c : Site) (rest : List Site)
 (s : NLM_Snapshot.State) (err : Error) (events : List NLM_Snapshot.Event)
 (head : NLM_Snapshot.G s c.account c.lo c.hi (allocation c)=⟨.fail err,events⟩) :
 NLM_SevenSnapshots.G allocation (c::rest) s=⟨.fail err,events⟩ := by
 rw [NLM_SevenSnapshots.G,head]
 rfl

theorem diverged (allocation : Site → Result Unit) (c : Site) (rest : List Site)
 (s : NLM_Snapshot.State) (events : List NLM_Snapshot.Event)
 (head : NLM_Snapshot.G s c.account c.lo c.hi (allocation c)=⟨.div,events⟩) :
 NLM_SevenSnapshots.G allocation (c::rest) s=⟨.div,events⟩ := by
 rw [NLM_SevenSnapshots.G,head]
 rfl
#print failed
#print diverged
#print axioms failed
#print axioms diverged
end NLM_SevenAbort
