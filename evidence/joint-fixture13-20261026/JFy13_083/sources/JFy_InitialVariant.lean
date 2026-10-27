import JFy_Steps
import FIq_Native10
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_InitialVariant
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open pool_v1.pair_forest_semantic_terminal

@[step] theorem source (v : CompiledVariant) (a b c : field.QM31) (ha : Canon a) (hb : Canon b) (hc : Canon c) :
    initial_variant_selectors v a b c ⦃ out => Canon out.1 ∧ Canon out.2.1 ∧ Canon out.2.2.1 ∧ Canon out.2.2.2 ⦄ := by
  have zero := FIv_NativeValue.zero.1
  cases v <;> simp only [initial_variant_selectors] <;> step*
  all_goals first | assumption | exact zero
#print axioms source
end AspisR1.JFy_InitialVariant
end
