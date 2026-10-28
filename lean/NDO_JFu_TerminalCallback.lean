import NDO_JFu_Claims
import RPu_FIq_Terminal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_TerminalCallback
open Aeneas Aeneas.Std Result WP
open FIq_Native
abbrev callback := pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut

def claims := FIq_Carriers.mapArray (FIq_Carriers.mapArray FIq_Carriers.toQ) JFu_ClaimsData.claims

theorem source (i : Usize) (bound : i.val<84) : ∃ q,callback claims i=ok (q,claims) := by
  have spec : callback claims i ⦃ out => out.2=claims ⦄ := by
    unfold callback pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    step* <;> scalar_tac
  obtain ⟨⟨q,after⟩,call,same⟩ := WP.spec_imp_exists spec
  exact ⟨q,same ▸ call⟩

#print axioms source
end AspisR1.JFu_TerminalCallback
end
