import PV_LIB_SPEC_Tls279History16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsAt67
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context initial)
open PV_LIB_SPEC_Tls64Data16 (at64 store64 result)
open PV_LIB_SPEC_TlsNative15 (cut)

def handler : Handler := PV_THR2_OwnUniformResourceHandler.lift
  PV_LIB_SPEC_ReachedEnvironment14.parameters.environment.native
def at67 : Execution := PV_LIB_SPEC_SourceTransport15.advance
  PV_LIB_SPEC_ReachedEnvironment14.parameters handler 3 at64

theorem result_bound : store64.cells ⟨5,5,[]⟩ = some result := by
  simp [store64,PV_STX2_Store.write]

theorem original67 (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 67
      (initial PV_LIB_SPEC_Entry14.input) = at67 := by
  rw [show 67=64+3 from rfl,PV_LIB_SPEC_Original14.run_add,PV_LIB_SPEC_TlsAt64.original64]
  exact PV_LIB_SPEC_SourceTransport15.run _ _ handler _ _
    (PV_LIB_SPEC_Tls279Request16.trace _ _ _ store64 5 PV_LIB_SPEC_TlsOriginal15.parents
      PV_LIB_SPEC_Entry14.state [] at64.issued at64.consumed)

theorem state67 : at67.state =
    ⟨⟨.running (PV_LIB_SPEC_Tls279Request16.config store64 5 PV_LIB_SPEC_TlsOriginal15.parents result),
      PV_LIB_SPEC_Entry14.state,[]⟩,[]⟩ := by
  unfold at67
  rw [PV_LIB_SPEC_SourceProjection15.state]
  exact PV_LIB_SPEC_Tls279Request16.source _ handler store64 5
    PV_LIB_SPEC_TlsOriginal15.parents result PV_LIB_SPEC_Entry14.state [] result_bound

theorem issued67 : at67.issued =
    (⟨PV_LIB_SPEC_Tls279History16.site,5,
      .child PV_THR2_RunTlsBranchRequest.callee 9 [result]⟩ : Issued) :: at64.issued :=
  PV_LIB_SPEC_Tls279History16.issued _ handler store64 5 PV_LIB_SPEC_TlsOriginal15.parents result
    PV_LIB_SPEC_Entry14.state [] at64.issued at64.consumed result_bound

theorem consumed67 : at67.consumed =
    [PV_LIB_SPEC_Tls64Data16.origin,PV_LIB_SPEC_Tls59Data15.origin,PV_LIB_SPEC_TlsAt55.origin] :=
  PV_LIB_SPEC_Tls279History16.consumed _ handler 3 at64

theorem world67 : at67.state.current.world = PV_LIB_SPEC_Entry14.state := by
  rw [state67]

theorem entry : OwnInit.Pre PV_LIB_SPEC_ReachedEnvironment14.parameters PV_LIB_SPEC_Entry14.input :=
  PV_LIB_SPEC_ReachedEnvironment14.pre

#print axioms handler
#print axioms at67
#print axioms result_bound
#print axioms original67
#print axioms state67
#print axioms issued67
#print axioms consumed67
#print axioms world67
#print axioms entry
end PV_LIB_SPEC_TlsAt67
