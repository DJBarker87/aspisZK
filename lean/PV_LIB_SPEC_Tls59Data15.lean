import PV_LIB_SPEC_Tls277Bound15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls59Data15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context)
open PV_LIB_SPEC_TlsNative15 (reference)

def token : Data := PV_LIB_SPEC_Tls277Native15.token
def result : Data := PV_LIB_SPEC_Tls277Native15.value PV_LIB_SPEC_Entry13.slot.source
def config : Config := PV_THR2_RunTlsNext.pending PV_LIB_SPEC_TlsDelivery15.store55 5
  PV_LIB_SPEC_TlsOriginal15.parents reference
def request : PV_STX2_Native.Request Data := .child token 7 [reference]
def wait : PV_STX2_Native.Waiting Data := ⟨request,.child 7 (.local 6),[]⟩
def origin : Context := ⟨PV_LIB_SPEC_Tls277Request15.site,0,[reference],5,request⟩
def store59 : Store Data := write (write config.store ⟨7,0,[]⟩ (some result)) ⟨5,6,[]⟩ (some result)
def after : State :=
  (PV_LIB_SPEC_F1Arithmetic14.stage store59 5 PV_LIB_SPEC_TlsOriginal15.parents
    (PV_THR2_F170.live.body.drop 17) PV_LIB_SPEC_Entry14.state [] [] []).state
def at59 : Execution := ⟨after,PV_LIB_SPEC_TlsAt58.at58.issued,
  [origin,PV_LIB_SPEC_TlsAt55.origin]⟩

theorem waiting : config.frame.waiting = some wait := rfl

theorem nonnative : PV_LIB_SPEC_ControlRuntime.ordinary PV_LIB_SPEC_TlsAt58.at58.state = some (config,wait) := by
  have lookup : PV_LIB_SPEC_Full.programs token = none := rfl
  simp [PV_LIB_SPEC_ControlRuntime.ordinary,PV_LIB_SPEC_TlsAt58.at58,
    PV_LIB_SPEC_Tls277Request15.after,config,wait,request,
    PV_THR2_RunTlsNext.pending,PV_THR2_RunTlsNext.callee,
    PV_THR2_Catch316Segment.select,lookup,token,PV_LIB_SPEC_Tls277Native15.token,
    show PV_LIB_SPEC_TlsDelivery15.store55.nextActivation=7 from rfl]
  exact lookup

#print axioms token
#print axioms result
#print axioms config
#print axioms request
#print axioms wait
#print axioms origin
#print axioms store59
#print axioms after
#print axioms at59
#print axioms waiting
#print axioms nonnative
end PV_LIB_SPEC_Tls59Data15
