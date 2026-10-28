import NDO_JFy_Preweighted
import RPv_JFy_Steps
import NDO_JFy_PublicCanonical
import RPv_FIw_ScalarSuffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_ScalarSuffix
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open JFy_PublicCanonical (p)

theorem source (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (s : pool_v1.pair_forest_copy_terminal.Selectors) (packed : Array field.QM31 24#usize)
    (hz : canonical o.z) (hh : canonical s.high) (hl : canonical s.low) (hp : canonical packed) :
    ∃ out,FIw_ScalarSuffix.run p o s packed=ok out ∧ canonical out := by
  have hab := JFy_PublicCanonical.asset
  have haw := JFy_PublicCanonical.amount
  have haw1 : (core.option.Option.unwrap_or p.withdrawal_amount 0#u32).val<2147483647 := by
    change (0:Nat)<2147483647
    omega
  have spec : FIw_ScalarSuffix.run p o s packed ⦃ out => canonical out ⦄ := by
    unfold FIw_ScalarSuffix.run pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK
    step* <;> first | assumption | scalar_tac
  exact WP.spec_imp_exists spec
#print axioms source
end AspisR1.JFy_ScalarSuffix
end
