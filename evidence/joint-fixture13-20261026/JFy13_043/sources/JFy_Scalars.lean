import JFy_Specs
import FIq_Native08
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_Scalars
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

theorem source (v : CompiledVariant) (present : Bool) (a b c d : field.QM31)
    (ha : Canon a) (hb : Canon b) (hc : Canon c) (hd : Canon d) :
    ∃ out,scalar_lanes v present a b c d=ok out ∧ canonical out := by
  have spec : scalar_lanes v present a b c d ⦃ out => canonical out ⦄ := by
    cases v <;> cases present <;> unfold scalar_lanes <;> step*
    all_goals intro x hx
    all_goals simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
    all_goals rcases hx with rfl | rfl <;> assumption
  exact WP.spec_imp_exists spec
#print axioms source
end AspisR1.JFy_Scalars
end
