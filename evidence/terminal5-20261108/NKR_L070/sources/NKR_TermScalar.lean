import NKI_InitialPrefix
import NDO_JFy_Preweighted
import RPv_JFy_Steps
import RPv_FIw_ScalarSuffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_TermScalar
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public Openings Selectors)
/--261 actual scalar tail at rows44,508,460,1010 and preweighted92.
Amount canonicality is an actual input clause, supplied after composition's
InvalidPublicAmount check; no selected child outcome is a hypothesis. -/
theorem source (pub : Public) (o : Openings) (s : Selectors) (packed : Array field.QM31 24#usize)
 (hz : canonical o.z) (hh : canonical s.high) (hl : canonical s.low) (hp : canonical packed)
 (asset : pub.asset_id.val<2147483647)
 (amount : (core.option.Option.unwrap_or pub.withdrawal_amount 0#u32).val<2147483647) :
 ∃ out,FIw_ScalarSuffix.run pub o s packed=ok out ∧ canonical out := by
 have spec : FIw_ScalarSuffix.run pub o s packed ⦃ out=>canonical out ⦄ := by
  unfold FIw_ScalarSuffix.run pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK
  step* <;> first | assumption | scalar_tac
 exact WP.spec_imp_exists spec
#print source
#print axioms source
end AspisR1.NKR_TermScalar
end
