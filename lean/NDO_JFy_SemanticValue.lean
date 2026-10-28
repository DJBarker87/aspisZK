import NDO_JFy_FrontierCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_SemanticValue
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical decoded)
open JFy_PublicCanonical (p)

theorem value (a b c : Array field.QM31 16#usize)
    (s : pool_v1.pair_forest_copy_terminal.Selectors) (out : Array field.QM31 24#usize)
    (ha : canonical a) (hb : canonical b) (hc : canonical c)
    (hh : canonical s.high) (hl : canonical s.low)
    (run : pool_v1.pair_forest_semantic_terminal.semantic_packed p ⟨a,b,c⟩ s=ok out) :
    canonical out ∧ decoded out=FIy_NativeCoefficients.model p ⟨a,b,c⟩ s := by
  exact FIy_NativeCoefficients.value p ⟨a,b,c⟩ s out ha hb hc hh hl
    JFy_PublicCanonical.anchor JFy_PublicCanonical.nullifier JFy_PublicCanonical.recipient JFy_PublicCanonical.change
    JFy_FrontierCanonical.before JFy_FrontierCanonical.root JFy_FrontierCanonical.after
    JFy_PublicCanonical.asset JFy_PublicCanonical.amount run
#print axioms value
end AspisR1.JFy_SemanticValue
end
