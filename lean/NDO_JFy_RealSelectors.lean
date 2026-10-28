import NDO_JFy_Selectors
import NDO_JFy_PointCanonical
import NDO_JFy_PoseidonSelectors
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_RealSelectors
open Aeneas Aeneas.Std Result FIq_Native

theorem source : ∃ s ps,
    pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point JFu_TerminalPrefix.alpha=ok s ∧
    FIw_ArrayValue.canonical s.high ∧ FIw_ArrayValue.canonical s.low ∧
    pool_v1.pair_forest_semantic_terminal.poseidon_selectors s=ok ps ∧
    FIv_NativeValue.Canon ps.block ∧ FIw_ArrayValue.canonical ps.«local» := by
  obtain ⟨s,hs,hh,hl⟩ := JFy_Selectors.source JFu_TerminalPrefix.alpha JFy_PointCanonical.source
  obtain ⟨ps,hps,hblock,hlocal⟩ := JFy_PoseidonSelectors.source s hh hl
  exact ⟨s,ps,hs,hh,hl,hps,hblock,hlocal⟩
#print axioms source
end AspisR1.JFy_RealSelectors
end
