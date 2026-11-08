import PV_LIB_SPEC_TlsLoad15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsOriginal15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory
open PV_LIB_SPEC_F1Arithmetic14 (stage)
open PV_LIB_SPEC_TlsOriginal14

def store40 : Store Data := PV_THR2_F17Call.issued withStore 4 ⟨3,2,[]⟩ PV_THR2_F2Call.descriptors.2
def parents : List Frame := PV_THR2_F17Call.parent withStore 4 ⟨3,2,[]⟩
  PV_THR2_F2Call.descriptors.2 :: withParents
def issued : List Issued := atTryWith.issued
def store50 : Store Data := PV_LIB_SPEC_TlsPoll15.prepared store40 5

theorem original50 (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 50
      (initial PV_LIB_SPEC_Entry14.input) =
    stage store50 5 parents (PV_THR2_F170.live.body.drop 10)
      PV_LIB_SPEC_Entry14.state [] issued [] := by
  rw [show 50=40+10 from rfl,PV_LIB_SPEC_Original14.run_add,original40]
  exact PV_LIB_SPEC_TlsPoll15.prepare cut _ store40 5 parents _ _ issued []

theorem key_bound : store50.cells ⟨5,1,[]⟩ =
    some (PV_STX2_TypedReferences.reference ⟨3,2,[]⟩ .null) := by
  simp [store50,PV_LIB_SPEC_TlsPoll15.prepared,store40,PV_THR2_F17Call.issued,
    PV_STX2_Native.arguments,PV_STX2_Store.write,
    show withStore.nextActivation=5 from rfl]

theorem key_read : readAddress (runtime PV_LIB_SPEC_ReachedEnvironment14.parameters).carrier
    store50 ⟨3,2,[]⟩ = some (PV_LIB_SPEC_TlsEntry14.key PV_LIB_SPEC_ReachedEnvironment14.parameters) := by
  change store50.cells ⟨3,2,[]⟩ = _
  simp [store50,PV_LIB_SPEC_TlsPoll15.prepared,store40,PV_THR2_F17Call.issued,
    PV_STX2_Native.arguments,PV_STX2_Store.write,PV_THR2_F17Prefix.prepared,
    withStore,PV_THR2_F2Call.issued,PV_THR2_F2Prefix.prepared,
    show workerStore.nextActivation=4 from rfl]

theorem original51 (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 51
      (initial PV_LIB_SPEC_Entry14.input) =
    PV_LIB_SPEC_TlsLoad15.after store50 5 (PV_THR2_KeyValues.castToken false).2 parents
      PV_LIB_SPEC_Entry14.state [] issued [] := by
  rw [show 51=50+1 from rfl,PV_LIB_SPEC_Original14.run_add,original50]
  exact PV_LIB_SPEC_TlsLoad15.load cut _ _ _ _ _ _ _ _ _ _ _ key_bound key_read rfl

#print axioms store40
#print axioms parents
#print axioms issued
#print axioms store50
#print axioms original50
#print axioms key_bound
#print axioms key_read
#print axioms original51
end PV_LIB_SPEC_TlsOriginal15
