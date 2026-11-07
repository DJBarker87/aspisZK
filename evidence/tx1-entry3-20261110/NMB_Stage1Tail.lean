import NMB_Stage1Source
set_option autoImplicit false
noncomputable section
namespace NMB_Stage1Tail
open Aeneas Aeneas.Std Result AspisR1 NMB_Stage1Source
def ready (x : NMB_Input.Input) : State := ⟨NMB_ThreeSnapshots.final x,none⟩
/-- Full source-state and event-prefix assembly at the SAME array returned by
all three snapshot occurrences. This is SOURCE support, not a native root. -/
theorem source (x : NMB_Input.Input) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) :
 G x ops p d (.ok ()) (.ok ()) (.ok ())=
 let tail := continuation ops p d (NMB_ThreeSnapshots.first x) (ready x)
 {tail with events:=(NMB_ThreeSnapshots.G x (.ok ()) (.ok ()) (.ok ())).events.map Event.snapshot++tail.events} := by
 simp only [G,NMB_ThreeSnapshots.result]
 rfl
#print source
#print axioms source
end NMB_Stage1Tail
