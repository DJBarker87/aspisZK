import PV_EVH_EntropyDeployedLayout
import PV_EVH_EntropyRejectCleanup
set_option autoImplicit false
namespace PV_EVH_EntropyLayoutCleanup
open PV_EVH_StackZero (State Cleared)
open PV_EVH_EntropyDeployedLayout (original field seed OutsideFrame)

/-- The existing rejected-iteration destructor law with all local numeric
FRAME inputs derived from the actual adopted layout. -/
theorem all_cleared (owner sp : Nat) (w : State) :
    let v := PV_EVH_EntropyRejectCleanup.cleanup (original owner sp w)
      (field owner sp w) (seed owner sp w) w
    Cleared (original owner sp w) v ∧ Cleared (field owner sp w) v ∧
      Cleared (seed owner sp w) v := by
  have h := PV_EVH_EntropyDeployedLayout.separation owner sp w
  exact PV_EVH_EntropyRejectCleanup.all_cleared _ _ _ w h.1.symm h.2.1.symm h.2.2.symm

/-- Actual entry heap coherence is HEAP-ENTRY, not supplied by ghost freshness.
The one external reserved-frame boundary derives all three destructor frames. -/
theorem heap_coherent (owner sp : Nat) (w : State)
    (hc : PV_EVH_StackAdmission.HeapCoherent w)
    (hh : ∀ b ∈ w.frame.runtime.heap, ∀ i, i < b.bytes.length →
      OutsideFrame sp (b.address+i)) :
    PV_EVH_StackAdmission.HeapCoherent
      (PV_EVH_EntropyRejectCleanup.cleanup (original owner sp w)
        (field owner sp w) (seed owner sp w) w) := by
  have h := PV_EVH_EntropyDeployedLayout.heap_frames owner sp w hh
  exact PV_EVH_EntropyRejectCleanup.heap_coherent _ _ _ w hc h.1 h.2.1 h.2.2

#print axioms all_cleared
#print axioms heap_coherent
end PV_EVH_EntropyLayoutCleanup
