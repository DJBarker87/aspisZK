import PV_LIB_SPEC_Tls18Reached16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls85Data16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context)
open PV_LIB_SPEC_TlsAt84 (config at84)
open PV_LIB_SPEC_Tls18Bound16 (token arguments request)

def wait : PV_STX2_Native.Waiting Data := ⟨request 10,.child 10 (.local 14),[]⟩
def origin : Context := ⟨PV_LIB_SPEC_TlsCallableHistory16.site,0,arguments,5,request 10⟩
def store85 : Store Data := write (write config.store ⟨10,0,[]⟩ (some (.boolean false)))
  ⟨5,14,[]⟩ (some (.boolean false))
def after : State := (PV_LIB_SPEC_F1Arithmetic14.stage store85 5
  PV_LIB_SPEC_TlsOriginal15.parents (PV_THR2_F170.live.body.drop 40)
  PV_LIB_SPEC_Entry14.state [] [] []).state
def at85 : Execution := ⟨after,at84.issued,origin :: at84.consumed⟩

theorem waiting : config.frame.waiting = some wait := rfl

theorem ordinary : PV_LIB_SPEC_ControlRuntime.ordinary at84.state = some (config,wait) := by
  rw [PV_LIB_SPEC_TlsAt84.state84]
  have lookup : PV_LIB_SPEC_Full.programs token = none := by
    have ne : token ≠ PV_THR2_Catch208Invoke.fn := by
      intro eq
      have same := congrArg PV_THR2_SourceTraitDispatch.source eq
      cases same
    change PV_THR2_Source208Table.table _ token = none
    rw [PV_THR2_Source208Table.away _ _ ne]
    rfl
  simp [PV_LIB_SPEC_ControlRuntime.ordinary,config,PV_LIB_SPEC_TlsCallable16.config,
    PV_THR2_Catch316Segment.select,wait,request,arguments,token,
    show PV_LIB_SPEC_TlsAt75.store75.nextActivation=10 from rfl]
  exact ⟨lookup,rfl⟩

#print axioms wait
#print axioms origin
#print axioms store85
#print axioms after
#print axioms at85
#print axioms waiting
#print axioms ordinary
end PV_LIB_SPEC_Tls85Data16
