import JFy_Steps
import JFy_BoundedCanonical
import FIx_Absorption
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_AbsorptionBuilder
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

theorem cell (fixed two eight nodes low : field.QM31) (a : Array field.QM31 16#usize) (i : Usize)
    (hi : i.val<16) (hf : Canon fixed) (ht : Canon two) (he : Canon eight) (hn : Canon nodes)
    (hl : Canon low) (ha : canonical a) :
    ∃ out,absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut (fixed,two,eight,nodes,low,a) i=
      ok (out,(fixed,two,eight,nodes,low,a)) ∧ Canon out := by
  have spec : absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut (fixed,two,eight,nodes,low,a) i
      ⦃ out => out.2=(fixed,two,eight,nodes,low,a) ∧ Canon out.1 ⦄ := by
    unfold absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    step* <;> first | assumption | scalar_tac
  obtain ⟨⟨out,last⟩,call,same,hout⟩ := WP.spec_imp_exists spec
  exact ⟨out,same ▸ call,hout⟩
#print axioms cell

@[step] theorem source (low fixed two eight nodes : field.QM31) (a : Array field.QM31 16#usize)
    (hf : Canon fixed) (ht : Canon two) (he : Canon eight) (hn : Canon nodes)
    (hl : Canon low) (ha : canonical a) :
    absorption_lanes_literal low fixed two eight nodes a ⦃ out => canonical out ⦄ := by
  apply exists_imp_spec
  unfold absorption_lanes_literal array_from_fn_copy
  apply JFy_BoundedCanonical.source
  intro i hi
  exact cell fixed two eight nodes low a i hi hf ht he hn hl ha
#print axioms source
end AspisR1.JFy_AbsorptionBuilder
end
