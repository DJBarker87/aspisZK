import PV_LIB_SPEC_Tls278History15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsAt63
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context initial)
open PV_LIB_SPEC_Tls59Data15 (at59 store59 result)
open PV_LIB_SPEC_TlsNative15 (cut)

def handler : Handler := PV_THR2_OwnUniformResourceHandler.lift
  PV_LIB_SPEC_ReachedEnvironment14.parameters.environment.native
def at63 : Execution := PV_LIB_SPEC_SourceTransport15.advance
  PV_LIB_SPEC_ReachedEnvironment14.parameters handler 4 at59

theorem result_bound : store59.cells ⟨5,6,[]⟩ = some result := by
  simp [store59,PV_STX2_Store.write]

theorem original63 (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 63
      (initial PV_LIB_SPEC_Entry14.input) = at63 := by
  rw [show 63=59+4 from rfl,PV_LIB_SPEC_Original14.run_add,PV_LIB_SPEC_TlsAt59.original59]
  exact PV_LIB_SPEC_SourceTransport15.run _ _ handler _ _
    (PV_LIB_SPEC_Tls278Trace15.trace _ _ _ store59 5 PV_LIB_SPEC_TlsOriginal15.parents
      PV_LIB_SPEC_Entry14.state [] PV_LIB_SPEC_TlsAt58.at58.issued
      [PV_LIB_SPEC_Tls59Data15.origin,PV_LIB_SPEC_TlsAt55.origin])

theorem state63 : at63.state =
    ⟨⟨.running (PV_LIB_SPEC_Tls278Lift15.config store59 5 PV_LIB_SPEC_TlsOriginal15.parents result),
      PV_LIB_SPEC_Entry14.state,[]⟩,[]⟩ := by
  unfold at63
  rw [PV_LIB_SPEC_SourceProjection15.state]
  exact PV_LIB_SPEC_Tls278Lift15.source _ handler store59 5
    PV_LIB_SPEC_TlsOriginal15.parents result PV_LIB_SPEC_Entry14.state [] result_bound

theorem issued63 : at63.issued =
    (⟨PV_LIB_SPEC_Tls278History15.site,5,
      .child PV_THR2_RunTlsErrorCompleted.callee 8 [result,PV_LIB_SPEC_Tls278Lift15.error]⟩ : Issued) :: at59.issued :=
  PV_LIB_SPEC_Tls278History15.issued _ handler store59 5 PV_LIB_SPEC_TlsOriginal15.parents result
    PV_LIB_SPEC_Entry14.state [] at59.issued at59.consumed result_bound

theorem consumed63 : at63.consumed =
    [PV_LIB_SPEC_Tls59Data15.origin,PV_LIB_SPEC_TlsAt55.origin] :=
  PV_LIB_SPEC_Tls278History15.consumed _ handler 4 at59

theorem world63 : at63.state.current.world = PV_LIB_SPEC_Entry14.state := by
  rw [state63]

theorem entry : OwnInit.Pre PV_LIB_SPEC_ReachedEnvironment14.parameters PV_LIB_SPEC_Entry14.input :=
  PV_LIB_SPEC_ReachedEnvironment14.pre

#print axioms handler
#print axioms at63
#print axioms result_bound
#print axioms original63
#print axioms state63
#print axioms issued63
#print axioms consumed63
#print axioms world63
#print axioms entry
end PV_LIB_SPEC_TlsAt63
