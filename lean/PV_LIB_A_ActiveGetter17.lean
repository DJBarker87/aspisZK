import PV_LIB_A_ActiveTransport17
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ActiveGetter17
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)
open PV_LIB_A_F5FullEntry16 (store activation parents keyAddress)

def store151 : Store Data := PV_LIB_SPEC_TlsPoll15.prepared store activation
def token : Data := (PV_THR2_KeyValues.castToken false).2
def store152 : Store Data := write store151 ⟨activation,8,[]⟩ (some token)
def init : Data := PV_THR2_KeyValues.pack PV_LIB_SPEC_TlsNone15.kind []
def store154 : Store Data := write (write store152 ⟨activation,9,[]⟩ none) ⟨activation,9,[]⟩ (some init)

theorem key_bound : store151.cells ⟨activation,1,[]⟩ =
    some (PV_STX2_TypedReferences.reference keyAddress .null) := by
  simp [store151,PV_LIB_SPEC_TlsPoll15.prepared,store,activation,PV_THR2_F17Call.issued,PV_THR2_F17Prefix.prepared,
    PV_STX2_Native.arguments,write,PV_LIB_A_F5FullEntry16.key_bound]

theorem key_read (p : Parameters) :
    readAddress (runtime p).carrier store151 keyAddress =
      some (PV_THR2_KeyInitConstruct.key PV_LIB_SPEC_ReachedEnvironment14.parameters.needsDrop) := by
  change store151.cells keyAddress = _
  simp [store151,PV_LIB_SPEC_TlsPoll15.prepared,store,PV_THR2_F17Call.issued,PV_THR2_F17Prefix.prepared,
    PV_LIB_A_F5FullPush16.store,PV_THR2_ActiveRequest.issued,PV_THR2_ActivePrefix.prepared,
    PV_STX2_Native.arguments,write,keyAddress,
    show activation=13 from rfl,
    show PV_LIB_A_F5FullPush16.activation=12 from rfl,
    show PV_LIB_A_F5FullPush16.store.nextActivation=13 from rfl,
    show PV_LIB_A_F5History16.store.nextActivation=12 from rfl,
    show PV_LIB_A_F5History16.activation=11 from rfl]

/-- Reuse the named TLS source contracts. They perform no native poll and
supply a fresh final source cut, permitting symbolic transport to the repair. -/
theorem retained154 (cut : PV_LIB_SPEC_ReachedNative14.Cut) (w : OWNER)
    (issued : List Issued) (consumed : List Context) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 13
      (stage store activation parents PV_THR2_F170.live.body w [] issued consumed) =
    stage store154 activation parents (PV_THR2_F170.live.body.drop 13) w [] issued consumed := by
  rw [show 13=10+(1+2) from rfl,PV_LIB_SPEC_Original14.run_add,
    PV_LIB_SPEC_TlsPoll15.prepare]
  change PV_LIB_SPEC_ReachedNative14.run cut _ (1+2)
    (stage store151 activation parents (PV_THR2_F170.live.body.drop 10) w [] issued consumed) = _
  rw [PV_LIB_SPEC_Original14.run_add,
    PV_LIB_SPEC_TlsLoad15.load cut _ store151 activation keyAddress _ token parents w [] issued consumed
      key_bound (key_read _) (by rfl)]
  exact PV_LIB_SPEC_TlsNone15.construct cut _ store152 activation parents w [] issued consumed

#print axioms key_bound
#print axioms key_read
#print axioms retained154
end PV_LIB_A_ActiveGetter17
