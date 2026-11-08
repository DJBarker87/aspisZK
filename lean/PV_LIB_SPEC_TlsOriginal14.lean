import PV_LIB_SPEC_F17Entry14
import PV_LIB_SPEC_Worker14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsOriginal14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory

def workerStore : Store Data := PV_THR2_F1Worker.issued PV_LIB_SPEC_Worker14.store 2
def workerParents : List Frame := PV_THR2_F1Worker.parent PV_LIB_SPEC_Worker14.store 2 ::
  PV_LIB_SPEC_F1Arithmetic14.parents
def workerIssued : List Issued := (PV_LIB_SPEC_Worker14.after PV_LIB_SPEC_Worker14.store 2
  PV_LIB_SPEC_F1Arithmetic14.parents PV_LIB_SPEC_Entry14.state [] PV_LIB_SPEC_F1Arithmetic14.issued []).issued

theorem original32 (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 32
      (initial PV_LIB_SPEC_Entry14.input) =
    PV_LIB_SPEC_TlsEntry14.after PV_LIB_SPEC_ReachedEnvironment14.parameters
      workerStore 3 workerParents PV_LIB_SPEC_Entry14.state [] workerIssued [] := by
  rw [show 32=25+7 from rfl,PV_LIB_SPEC_Original14.run_add,PV_LIB_SPEC_Worker14.original]
  exact PV_LIB_SPEC_TlsEntry14.enter cut _ _ _ _ _ _ _ _

def withStore : Store Data := PV_THR2_F2Call.issued workerStore 3
  (PV_LIB_SPEC_TlsEntry14.key PV_LIB_SPEC_ReachedEnvironment14.parameters)
  PV_THR2_F2Call.descriptors.2
def withParents : List Frame :=
  PV_THR2_F2Child.parent workerStore 3 PV_THR2_F2Call.descriptors.2 :: workerParents
def withIssued : List Issued := (PV_LIB_SPEC_TlsEntry14.after PV_LIB_SPEC_ReachedEnvironment14.parameters
  workerStore 3 workerParents PV_LIB_SPEC_Entry14.state [] workerIssued []).issued

def atTryWith : Execution := PV_LIB_SPEC_F17Entry14.after withStore 4 ⟨3,2,[]⟩
  PV_THR2_F2Call.descriptors.2 withParents PV_LIB_SPEC_Entry14.state [] withIssued []

/-- Continuous40-step prefix from the SAME initialized original entry, through
both emitted BODY pushes, at try_with170 entry. No native answer has yet been
consumed; no native stack pairing, successful295/454 reachability or cut92 is
inferred from this source-only prefix. -/
theorem original40 (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 40
      (initial PV_LIB_SPEC_Entry14.input) = atTryWith := by
  rw [show 40=32+8 from rfl,PV_LIB_SPEC_Original14.run_add,original32]
  apply PV_LIB_SPEC_F17Entry14.enter
  · simp [withStore,PV_THR2_F2Call.issued,PV_THR2_F2Prefix.prepared,
      PV_STX2_Native.arguments,PV_STX2_Store.write,
      show workerStore.nextActivation = 4 from rfl]
  · simp [withStore,PV_THR2_F2Call.issued,PV_THR2_F2Prefix.prepared,
      PV_STX2_Native.arguments,PV_STX2_Store.write,
      show workerStore.nextActivation = 4 from rfl]

theorem world40 (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    (PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 40
      (initial PV_LIB_SPEC_Entry14.input)).state.current.world = PV_LIB_SPEC_Entry14.state := by
  rw [original40]
  rfl

theorem no_native40 (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    (PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 40
      (initial PV_LIB_SPEC_Entry14.input)).consumed = [] := by
  rw [original40]
  rfl

#print axioms workerStore
#print axioms workerParents
#print axioms workerIssued
#print axioms original32
#print axioms withStore
#print axioms withParents
#print axioms withIssued
#print axioms atTryWith
#print axioms original40
#print axioms world40
#print axioms no_native40
end PV_LIB_SPEC_TlsOriginal14
