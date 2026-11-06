import NLM_SevenAbort
set_option autoImplicit false
noncomputable section
namespace NLM_SevenAbortAt
open Aeneas Aeneas.Std NLM_Snapshot NLM_SevenSnapshots
/-- Arbitrary occurrence, without a chosen prefix transcript or skipped
snapshot. The two premises are precisely the two local entered cuts. -/
theorem failed (allocation : Site → Result Unit) (xs rest : List Site) (c : Site)
 (s mid : NLM_Snapshot.State) (err : Error) (before tail : List NLM_Snapshot.Event)
 (completed : NLM_SevenSnapshots.G allocation xs s=⟨.ok mid,before⟩)
 (halt : NLM_Snapshot.G mid c.account c.lo c.hi (allocation c)=⟨.fail err,tail⟩) :
 NLM_SevenSnapshots.G allocation (xs++c::rest) s=⟨.fail err,before++tail⟩ := by
 rw [NLM_SevenSplit.split,completed]
 change (⟨(NLM_SevenSnapshots.G allocation (c::rest) mid).result,before++(NLM_SevenSnapshots.G allocation (c::rest) mid).events⟩ :
  NLM_Snapshot.Run NLM_Snapshot.State)=_
 rw [NLM_SevenAbort.failed allocation c rest mid err tail halt]
#print failed
#print axioms failed
end NLM_SevenAbortAt
