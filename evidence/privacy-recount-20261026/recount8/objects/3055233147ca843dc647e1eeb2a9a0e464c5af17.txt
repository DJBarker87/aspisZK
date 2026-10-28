import R1Z.PV_RW_IteratorStateSource
import R1Z.PV_RW_CompressNativeState
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_IteratorStateLoop
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Q := aspis_core.field.QM31
abbrev Iter := core.slice.iter.Iter U32
variable [ExternalTypes]

def run (ops : ExternalFuns) (lambda : Q) (iterator : Iter) (state : Q × Q) : Result (Q × Q) :=
  Aeneas.Std.loop (fun pair => @PV_RW_IteratorStateSource.body _ (PV_CurrentScaleInstall.selected ops)
    lambda pair.1 pair.2) (iterator,state)

theorem control (ops : ExternalFuns) (lambda : Q) (iterator : Iter) (state : Q × Q) :
    run ops lambda iterator state=
      PV_RW_NativeForSource.run (PV_RW_CompressNativeState.step ops lambda) iterator state := by
  unfold run PV_RW_NativeForSource.run
  have bodies : (fun pair : Iter × (Q × Q) =>
      @PV_RW_IteratorStateSource.body _ (PV_CurrentScaleInstall.selected ops) lambda pair.1 pair.2)=
      (fun pair : Iter × (Q × Q) =>
        PV_RW_NativeForSource.body (PV_RW_CompressNativeState.step ops lambda) pair.1 pair.2) := by
    funext pair
    exact @PV_RW_IteratorStateSource.control _ (PV_CurrentScaleInstall.selected ops) lambda pair.1 pair.2
  rw [bodies]

theorem owned (ops : ExternalFuns) (lambda : Q) (values : Slice U32) (state : Q × Q) :
    run ops lambda (⟨values,0⟩ : Iter) state=PV_RW_CompressClosedFold.owned values.val lambda state :=
  (control ops lambda _ state).trans (PV_RW_CompressNativeState.whole_state ops values lambda state)

-- This loop is assembled from the emitted combined transition. The original
-- whole Rust helper's source association remains a separate open obligation.
#print axioms control
#print axioms owned
end R1Z.PV_RW_IteratorStateLoop
