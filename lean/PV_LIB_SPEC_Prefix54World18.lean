import PV_LIB_SPEC_EntryWorld18
import PV_LIB_SPEC_TlsAt85
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Prefix54World18
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory

theorem original6 (w : OWNER) (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 6
      (initial (PV_LIB_SPEC_EntryWorld18.input w)) =
    PV_LIB_SPEC_Original14.after PV_LIB_SPEC_Entry13.store 1 1 PV_LIB_SPEC_ConcreteCaptures.closure
      w [] :=
  PV_LIB_SPEC_Original14.request cut _ _ _ _ _ _ _ rfl rfl rfl

#print axioms original6

theorem original7 (w : OWNER) (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 7
      (initial (PV_LIB_SPEC_EntryWorld18.input w)) =
    PV_LIB_SPEC_Original14.bodyEntry PV_LIB_SPEC_Entry13.store 1 1 PV_LIB_SPEC_ConcreteCaptures.closure
      w [] := by
  rw [show 7=6+1 from rfl,PV_LIB_SPEC_Original14.run_add,original6]
  exact PV_LIB_SPEC_Original14.enter cut _ _ _ _ _ _ _

#print axioms original7

theorem original13 (w : OWNER) (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 13
      (initial (PV_LIB_SPEC_EntryWorld18.input w)) =
    PV_LIB_SPEC_F1Prefix14.after (PV_FN_THREAD_f0Entry.issued PV_LIB_SPEC_Entry13.store 1 (.number 1)
      PV_LIB_SPEC_ConcreteCaptures.closure (.boolean true)) 2
      [PV_FN_THREAD_f0Entry.parent PV_LIB_SPEC_Entry13.store 1 (.number 1)
        PV_LIB_SPEC_ConcreteCaptures.closure (.boolean true)] (.number 1)
      w []
      (PV_LIB_SPEC_Original14.after PV_LIB_SPEC_Entry13.store 1 1
        PV_LIB_SPEC_ConcreteCaptures.closure w []).issued [] := by
  rw [show 13=7+6 from rfl,PV_LIB_SPEC_Original14.run_add,original7]
  apply PV_LIB_SPEC_F1Prefix14.prepare
  simp [PV_FN_THREAD_f0Entry.issued,PV_FN_THREAD_f0Entry.prepared,PV_THR2_StaticCall.issued,
    PV_STX2_Native.arguments,PV_STX2_Store.write]

#print axioms original13

theorem original16 (w : OWNER) (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 16
      (initial (PV_LIB_SPEC_EntryWorld18.input w)) =
    PV_LIB_SPEC_F1Arithmetic14.after PV_LIB_SPEC_F1Arithmetic14.store 2 PV_LIB_SPEC_F1Arithmetic14.parents 1 w [] PV_LIB_SPEC_F1Arithmetic14.issued [] := by
  rw [show 16=13+3 from rfl,PV_LIB_SPEC_Original14.run_add,original13]
  apply PV_LIB_SPEC_F1Arithmetic14.comparison
  simp [PV_LIB_SPEC_F1Arithmetic14.store,PV_FN_THREAD_f1Entry.prepared,PV_STX2_Store.write]

#print axioms original16

theorem original22 (w : OWNER) (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 22
      (initial (PV_LIB_SPEC_EntryWorld18.input w)) =
    PV_LIB_SPEC_F1Force14.after PV_LIB_SPEC_F1Force14.store 2 PV_LIB_SPEC_F1Arithmetic14.parents w []
      PV_LIB_SPEC_F1Arithmetic14.issued [] := by
  rw [show 22=16+6 from rfl,PV_LIB_SPEC_Original14.run_add,original16]
  apply PV_LIB_SPEC_F1Force14.forced
  · exact PV_STX2_Store.write_same _ _ _
  · simp [PV_LIB_SPEC_F1Force14.store,PV_THR2_F1Arithmetic.compared,PV_LIB_SPEC_F1Arithmetic14.store,
      PV_FN_THREAD_f1Entry.prepared,PV_FN_THREAD_f0Entry.issued,PV_FN_THREAD_f0Entry.prepared,
      PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,PV_STX2_Store.write,
      show PV_LIB_SPEC_Entry13.store.nextActivation = 2 from rfl]

#print axioms original22

theorem original25 (w : OWNER) (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 25
      (initial (PV_LIB_SPEC_EntryWorld18.input w)) =
    PV_LIB_SPEC_Worker14.after PV_LIB_SPEC_Worker14.store 2 PV_LIB_SPEC_F1Arithmetic14.parents w []
      PV_LIB_SPEC_F1Arithmetic14.issued [] := by
  rw [show 25=22+3 from rfl,PV_LIB_SPEC_Original14.run_add,original22]
  exact PV_LIB_SPEC_Worker14.enter cut _ _ _ _ _ _ _ _

#print axioms original25

theorem original32 (w : OWNER) (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 32
      (initial (PV_LIB_SPEC_EntryWorld18.input w)) =
    PV_LIB_SPEC_TlsEntry14.after PV_LIB_SPEC_ReachedEnvironment14.parameters
      PV_LIB_SPEC_TlsOriginal14.workerStore 3 PV_LIB_SPEC_TlsOriginal14.workerParents w [] PV_LIB_SPEC_TlsOriginal14.workerIssued [] := by
  rw [show 32=25+7 from rfl,PV_LIB_SPEC_Original14.run_add,original25]
  exact PV_LIB_SPEC_TlsEntry14.enter cut _ _ _ _ _ _ _ _

#print axioms original32

theorem original40 (w : OWNER) (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 40
      (initial (PV_LIB_SPEC_EntryWorld18.input w)) =
    PV_LIB_SPEC_F17Entry14.after PV_LIB_SPEC_TlsOriginal14.withStore 4 ⟨3,2,[]⟩
      PV_THR2_F2Call.descriptors.2 PV_LIB_SPEC_TlsOriginal14.withParents w []
      PV_LIB_SPEC_TlsOriginal14.withIssued [] := by
  rw [show 40=32+8 from rfl,PV_LIB_SPEC_Original14.run_add,original32]
  apply PV_LIB_SPEC_F17Entry14.enter
  · simp [PV_LIB_SPEC_TlsOriginal14.withStore,PV_THR2_F2Call.issued,PV_THR2_F2Prefix.prepared,
      PV_STX2_Native.arguments,PV_STX2_Store.write,
      show PV_LIB_SPEC_TlsOriginal14.workerStore.nextActivation = 4 from rfl]
  · simp [PV_LIB_SPEC_TlsOriginal14.withStore,PV_THR2_F2Call.issued,PV_THR2_F2Prefix.prepared,
      PV_STX2_Native.arguments,PV_STX2_Store.write,
      show PV_LIB_SPEC_TlsOriginal14.workerStore.nextActivation = 4 from rfl]

#print axioms original40

theorem original50 (w : OWNER) (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 50
      (initial (PV_LIB_SPEC_EntryWorld18.input w)) =
    PV_LIB_SPEC_F1Arithmetic14.stage PV_LIB_SPEC_TlsOriginal15.store50 5 PV_LIB_SPEC_TlsOriginal15.parents (PV_THR2_F170.live.body.drop 10)
      w [] PV_LIB_SPEC_TlsOriginal15.issued [] := by
  rw [show 50=40+10 from rfl,PV_LIB_SPEC_Original14.run_add,original40]
  exact PV_LIB_SPEC_TlsPoll15.prepare cut _ PV_LIB_SPEC_TlsOriginal15.store40 5 PV_LIB_SPEC_TlsOriginal15.parents _ _ PV_LIB_SPEC_TlsOriginal15.issued []

#print axioms original50

theorem original51 (w : OWNER) (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 51
      (initial (PV_LIB_SPEC_EntryWorld18.input w)) =
    PV_LIB_SPEC_TlsLoad15.after PV_LIB_SPEC_TlsOriginal15.store50 5 (PV_THR2_KeyValues.castToken false).2 PV_LIB_SPEC_TlsOriginal15.parents
      w [] PV_LIB_SPEC_TlsOriginal15.issued [] := by
  rw [show 51=50+1 from rfl,PV_LIB_SPEC_Original14.run_add,original50]
  exact PV_LIB_SPEC_TlsLoad15.load cut _ _ _ _ _ _ _ _ _ _ _ PV_LIB_SPEC_TlsOriginal15.key_bound PV_LIB_SPEC_TlsOriginal15.key_read rfl

#print axioms original51

theorem original53 (w : OWNER) (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 53
      (initial (PV_LIB_SPEC_EntryWorld18.input w)) =
    PV_LIB_SPEC_F1Arithmetic14.stage PV_LIB_SPEC_TlsAt54.store53 5 PV_LIB_SPEC_TlsOriginal15.parents (PV_THR2_F170.live.body.drop 13)
      w [] PV_LIB_SPEC_TlsOriginal15.issued [] := by
  rw [show 53=51+2 from rfl,PV_LIB_SPEC_Original14.run_add,original51]
  exact PV_LIB_SPEC_TlsNone15.construct cut _ PV_LIB_SPEC_TlsAt54.store51 5 PV_LIB_SPEC_TlsOriginal15.parents _ _ PV_LIB_SPEC_TlsOriginal15.issued []

#print axioms original53

theorem original54 (w : OWNER) (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 54
      (initial (PV_LIB_SPEC_EntryWorld18.input w)) =
    PV_LIB_SPEC_TlsRequest15.after PV_LIB_SPEC_TlsAt54.store53 5 PV_LIB_SPEC_TlsAt54.token
      PV_LIB_SPEC_TlsAt54.initValue PV_LIB_SPEC_TlsOriginal15.parents w []
      PV_LIB_SPEC_TlsOriginal15.issued [] := by
  rw [show 54=53+1 from rfl,PV_LIB_SPEC_Original14.run_add,original53]
  apply PV_LIB_SPEC_TlsRequest15.request
  · simp [PV_LIB_SPEC_TlsAt54.store53,PV_LIB_SPEC_TlsAt54.store51,PV_STX2_Store.write]
  · simp [PV_LIB_SPEC_TlsAt54.store53,PV_STX2_Store.write]

#print axioms original54
end PV_LIB_SPEC_Prefix54World18
