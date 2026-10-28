import NDO_JFu_TerminalCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_TerminalCallbackCanonical
open Aeneas Aeneas.Std Result WP FIq_Native
open JFu_TerminalCallback

theorem source (position : Usize) (bound : position.val<84) :
    ∃ q,callback claims position=ok (q,claims) ∧ JFu_TerminalCanonical.Canon q := by
  have spec : callback claims position ⦃ out => out.2=claims ∧ JFu_TerminalCanonical.Canon out.1 ⦄ := by
    unfold callback pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    step*
    all_goals first
      | scalar_tac
      | (have hcell := JFu_TerminalCanonical.source
             ⟨position.val/28,by omega⟩ ⟨position.val%28,by omega⟩
         simpa only [*] using hcell)
  obtain ⟨⟨q,after⟩,call,same,canonical⟩ := WP.spec_imp_exists spec
  exact ⟨q,same ▸ call,canonical⟩
#print axioms source
end AspisR1.JFy_TerminalCallbackCanonical
end
