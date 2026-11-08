import PV_LIB_SPEC_TlsAt67
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls68Data16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context)
open PV_LIB_SPEC_TlsNative15 (reference)

def token : Data := PV_LIB_SPEC_Tls279Values16.token
def result : Data := PV_LIB_SPEC_Tls279Values16.value PV_LIB_SPEC_Entry13.slot.source
def config : Config := PV_LIB_SPEC_Tls279Request16.config PV_LIB_SPEC_Tls64Data16.store64 5
  PV_LIB_SPEC_TlsOriginal15.parents PV_LIB_SPEC_Tls64Data16.result
def request : PV_STX2_Native.Request Data := .child token 9 [PV_LIB_SPEC_Tls64Data16.result]
def wait : PV_STX2_Native.Waiting Data := ⟨request,.child 9 (.local 4),[]⟩
def origin : Context := ⟨PV_LIB_SPEC_Tls279History16.site,0,[PV_LIB_SPEC_Tls64Data16.result],5,request⟩
def store68 : Store Data := write (write config.store ⟨9,0,[]⟩ (some result)) ⟨5,4,[]⟩ (some result)
def after : State :=
  (PV_LIB_SPEC_F1Arithmetic14.stage store68 5 PV_LIB_SPEC_TlsOriginal15.parents
    (PV_THR2_F170.live.body.drop 24) PV_LIB_SPEC_Entry14.state [] [] []).state
def at68 : Execution := ⟨after,PV_LIB_SPEC_TlsAt67.at67.issued,
  origin :: PV_LIB_SPEC_TlsAt67.at67.consumed⟩

theorem waiting : config.frame.waiting = some wait := rfl

theorem nonnative : PV_LIB_SPEC_ControlRuntime.ordinary PV_LIB_SPEC_TlsAt67.at67.state = some (config,wait) := by
  rw [PV_LIB_SPEC_TlsAt67.state67]
  have lookup : PV_LIB_SPEC_Full.programs token = none := rfl
  simp [PV_LIB_SPEC_ControlRuntime.ordinary,config,wait,request,
    PV_LIB_SPEC_Tls279Request16.config,PV_THR2_RunTlsBranchRequest.pending,
    PV_THR2_Catch316Segment.select,token,PV_LIB_SPEC_Tls279Values16.token,
    show PV_LIB_SPEC_Tls64Data16.store64.nextActivation=9 from rfl]

  exact lookup

#print axioms token
#print axioms result
#print axioms config
#print axioms request
#print axioms wait
#print axioms origin
#print axioms store68
#print axioms after
#print axioms at68
#print axioms waiting
#print axioms nonnative
end PV_LIB_SPEC_Tls68Data16
