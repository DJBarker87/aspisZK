import PV_LIB_SPEC_TlsForwardLift16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsAt75
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution initial)
open PV_LIB_SPEC_TlsNative15 (cut reference)
open PV_LIB_SPEC_Tls68Data16 (at68 store68 result)

def handler : Handler := PV_LIB_SPEC_TlsAt67.handler
def store75 : Store Data := PV_LIB_SPEC_TlsForward16.prepared store68 5 reference
def at75 : Execution := PV_LIB_SPEC_SourceTransport15.advance
  PV_LIB_SPEC_ReachedEnvironment14.parameters handler 7 at68

theorem cell : store68.cells ⟨5,4,[]⟩ = some result := by
  simp [store68,write]

theorem original75 (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 75
      (initial PV_LIB_SPEC_Entry14.input) = at75 := by
  rw [show 75=68+7 from rfl,PV_LIB_SPEC_Original14.run_add,PV_LIB_SPEC_TlsAt68.original68]
  exact PV_LIB_SPEC_SourceTransport15.run _ _ handler _ _
    (PV_LIB_SPEC_TlsForward16.trace _ _ _ store68 5 PV_LIB_SPEC_TlsOriginal15.parents
      PV_LIB_SPEC_Entry14.state [] at68.issued at68.consumed result reference cell rfl rfl)

theorem state75 : at75.state =
    ⟨⟨.running ⟨{activation := 5,remaining := PV_THR2_F170.live.body.drop 31},
      PV_LIB_SPEC_TlsOriginal15.parents,store75⟩,PV_LIB_SPEC_Entry14.state,[]⟩,[]⟩ := by
  unfold at75
  rw [PV_LIB_SPEC_SourceProjection15.state]
  exact PV_LIB_SPEC_TlsForwardLift16.source _ handler store68 5
    PV_LIB_SPEC_TlsOriginal15.parents result reference PV_LIB_SPEC_Entry14.state [] cell rfl rfl

theorem consumed75 : at75.consumed = at68.consumed :=
  PV_LIB_SPEC_Tls279History16.consumed _ handler 7 at68

#print axioms handler
#print axioms store75
#print axioms at75
#print axioms cell
#print axioms original75
#print axioms state75
#print axioms consumed75
end PV_LIB_SPEC_TlsAt75
