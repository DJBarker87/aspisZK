import PV_LIB_SPEC_Tls278Reached15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls64Data16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context)
open PV_LIB_SPEC_TlsNative15 (reference)

def token : Data := PV_LIB_SPEC_Tls278Values15.token
def result : Data := PV_LIB_SPEC_Tls278Values15.value PV_LIB_SPEC_Entry13.slot.source
def config : Config := PV_LIB_SPEC_Tls278Reached15.config
def request : PV_STX2_Native.Request Data := PV_LIB_SPEC_Tls278Reached15.request
def wait : PV_STX2_Native.Waiting Data := PV_LIB_SPEC_Tls278Reached15.wait
def origin : Context := ⟨PV_LIB_SPEC_Tls278History15.site,0,
  [PV_LIB_SPEC_Tls59Data15.result,PV_LIB_SPEC_Tls278Lift15.error],5,request⟩
def store64 : Store Data := write (write config.store ⟨8,0,[]⟩ (some result)) ⟨5,5,[]⟩ (some result)
def after : State :=
  (PV_LIB_SPEC_F1Arithmetic14.stage store64 5 PV_LIB_SPEC_TlsOriginal15.parents
    (PV_THR2_F170.live.body.drop 21) PV_LIB_SPEC_Entry14.state [] [] []).state
def at64 : Execution := ⟨after,PV_LIB_SPEC_TlsAt63.at63.issued,
  origin :: PV_LIB_SPEC_TlsAt63.at63.consumed⟩

theorem waiting : config.frame.waiting = some wait := rfl

theorem nonnative : PV_LIB_SPEC_ControlRuntime.ordinary PV_LIB_SPEC_TlsAt63.at63.state = some (config,wait) := by
  rw [PV_LIB_SPEC_TlsAt63.state63]
  have lookup : PV_LIB_SPEC_Full.programs token = none := rfl
  simp [PV_LIB_SPEC_ControlRuntime.ordinary,config,wait,request,
    PV_LIB_SPEC_Tls278Reached15.config,PV_LIB_SPEC_Tls278Reached15.wait,
    PV_LIB_SPEC_Tls278Reached15.request,PV_LIB_SPEC_Tls278Lift15.config,
    PV_THR2_Catch316Segment.select,token,PV_LIB_SPEC_Tls278Values15.token,
    show PV_LIB_SPEC_Tls59Data15.store59.nextActivation=8 from rfl]
  exact lookup

#print axioms token
#print axioms result
#print axioms config
#print axioms request
#print axioms wait
#print axioms origin
#print axioms store64
#print axioms after
#print axioms at64
#print axioms waiting
#print axioms nonnative
end PV_LIB_SPEC_Tls64Data16
