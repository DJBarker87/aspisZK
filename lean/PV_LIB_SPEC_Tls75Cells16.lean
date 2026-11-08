import PV_LIB_SPEC_TlsAt75
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls75Cells16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_TlsAt75 (store75)
open PV_LIB_SPEC_TlsNative15 (reference)

theorem pointer : store75.cells ⟨5,3,[]⟩ = some reference := by
  simp [store75,PV_LIB_SPEC_TlsForward16.prepared,PV_THR2_RunTlsForward.prepared,write]

theorem callable : store75.cells ⟨5,2,[]⟩ = some PV_THR2_F2Call.descriptors.2 := by
  simp [store75,PV_LIB_SPEC_TlsForward16.prepared,PV_THR2_RunTlsForward.prepared,
    PV_LIB_SPEC_Tls68Data16.store68,PV_LIB_SPEC_Tls68Data16.config,
    PV_LIB_SPEC_Tls279Request16.config,PV_THR2_RunTlsBranchRequest.pending,
    PV_THR2_RunTlsBranchRequest.issued,PV_LIB_SPEC_Tls64Data16.store64,
    PV_LIB_SPEC_Tls64Data16.config,PV_LIB_SPEC_Tls278Reached15.config,
    PV_LIB_SPEC_Tls278Lift15.config,PV_THR2_RunTlsErrorCompleted.issued,
    PV_LIB_SPEC_Tls59Data15.store59,PV_LIB_SPEC_Tls59Data15.config,
    PV_THR2_RunTlsNext.pending,PV_THR2_RunTlsNext.issued,
    PV_LIB_SPEC_TlsDelivery15.store55,PV_LIB_SPEC_TlsAt54.config,
    PV_LIB_SPEC_TlsRequest15.issuedStore,PV_LIB_SPEC_TlsAt54.store53,
    PV_LIB_SPEC_TlsAt54.store51,PV_LIB_SPEC_TlsOriginal15.store50,
    PV_LIB_SPEC_TlsPoll15.prepared,PV_LIB_SPEC_TlsOriginal15.store40,
    PV_THR2_F17Call.issued,PV_STX2_Native.arguments,write,
    show PV_LIB_SPEC_TlsOriginal14.withStore.nextActivation=5 from rfl,
    show PV_LIB_SPEC_TlsDelivery15.store55.nextActivation=7 from rfl,
    show PV_LIB_SPEC_Tls59Data15.store59.nextActivation=8 from rfl,
    show PV_LIB_SPEC_Tls64Data16.store64.nextActivation=9 from rfl]

#print axioms pointer
#print axioms callable
end PV_LIB_SPEC_Tls75Cells16
