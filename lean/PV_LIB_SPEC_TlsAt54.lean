import PV_LIB_SPEC_TlsRequest15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsAt54
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory
open PV_LIB_SPEC_F1Arithmetic14 (stage)
open PV_LIB_SPEC_TlsOriginal15

def token : Data := (PV_THR2_KeyValues.castToken false).2
def initValue : Data := PV_THR2_KeyValues.pack PV_LIB_SPEC_TlsNone15.kind []
def store51 : Store Data := write store50 ⟨5,8,[]⟩ (some token)
def store53 : Store Data := write (write store51 ⟨5,9,[]⟩ none) ⟨5,9,[]⟩ (some initValue)
def at54 : Execution := PV_LIB_SPEC_TlsRequest15.after store53 5 token initValue parents
  PV_LIB_SPEC_Entry14.state [] issued []

theorem original53 (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 53
      (initial PV_LIB_SPEC_Entry14.input) =
    stage store53 5 parents (PV_THR2_F170.live.body.drop 13)
      PV_LIB_SPEC_Entry14.state [] issued [] := by
  rw [show 53=51+2 from rfl,PV_LIB_SPEC_Original14.run_add,original51]
  exact PV_LIB_SPEC_TlsNone15.construct cut _ store51 5 parents _ _ issued []

theorem original54 (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 54
      (initial PV_LIB_SPEC_Entry14.input) = at54 := by
  rw [show 54=53+1 from rfl,PV_LIB_SPEC_Original14.run_add,original53]
  apply PV_LIB_SPEC_TlsRequest15.request
  · simp [store53,store51,PV_STX2_Store.write]
  · simp [store53,PV_STX2_Store.write]

def config : Config := ⟨{activation := 5,remaining := PV_THR2_F170.live.body.drop 14, waiting := some ⟨.child token 6 [initValue],.child 6 (.local 7),[]⟩},
  parents,PV_LIB_SPEC_TlsRequest15.issuedStore store53 5 initValue⟩

theorem reached_poll : at54.state.current.status = .running config := rfl

theorem world54 (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    (PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 54
      (initial PV_LIB_SPEC_Entry14.input)).state.current.world = PV_LIB_SPEC_Entry14.state := by
  rw [original54]; rfl

theorem no_native54 (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    (PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 54
      (initial PV_LIB_SPEC_Entry14.input)).consumed = [] := by
  rw [original54]; rfl

#print axioms token
#print axioms initValue
#print axioms store51
#print axioms store53
#print axioms at54
#print axioms original53
#print axioms original54
#print axioms config
#print axioms reached_poll
#print axioms world54
#print axioms no_native54
end PV_LIB_SPEC_TlsAt54
