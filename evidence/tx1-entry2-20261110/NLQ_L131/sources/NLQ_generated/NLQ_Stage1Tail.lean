import NLQ_Stage1Fold
import NLQ_Stage1Ready
set_option autoImplicit false
noncomputable section
namespace NLQ_Stage1Tail
open Aeneas Aeneas.Std Result AspisR1 NLQ_Stage1State
/-- Full post and chronology at the actual normal snapshot boundary. This
is stronger than projecting Result, and retains a computed full child tail. -/
theorem source (e : S2W_D189Entry.Entry) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) :
 NLQ_Stage1Fold.G e ops p d (.ok ()) (.ok ()) (.ok ()) =
 let tail := continuation ops p d (NLQ_Stage1Ready.initial e)
 {tail with events:=(NLQ_SnapshotFold.G e (.ok ()) (.ok ()) (.ok ())).events.map Event.snapshot++tail.events} := by
 simp only [NLQ_Stage1Fold.G,NLQ_SnapshotFold.returned]
 rfl
#print source
#print axioms source
end NLQ_Stage1Tail
