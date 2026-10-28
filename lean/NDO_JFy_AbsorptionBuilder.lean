import RPv_JFy_Steps
import NDO_JFy_BoundedCanonical
import RPv_FIx_Absorption
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_AbsorptionBuilder
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

@[step] theorem blocks (fixed two eight nodes : field.QM31) (i : Usize)
    (hf : Canon fixed) (ht : Canon two) (he : Canon eight) (hn : Canon nodes) :
    FIx_Absorption.blockRun fixed two eight nodes i ⦃ out => Canon out ⦄ := by
  unfold FIx_Absorption.blockRun
  by_cases h2 : i<2#usize <;> by_cases h8 : i<poseidon2.RATE
  all_goals simp only [h2,h8,↓reduceIte]
  all_goals step* <;> assumption
#print axioms blocks

theorem cell (fixed two eight nodes low : field.QM31) (a : Array field.QM31 16#usize) (i : Usize)
    (hi : i.val<16) (hf : Canon fixed) (ht : Canon two) (he : Canon eight) (hn : Canon nodes)
    (hl : Canon low) (ha : canonical a) :
    ∃ out,absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut (fixed,two,eight,nodes,low,a) i=
      ok (out,(fixed,two,eight,nodes,low,a)) ∧ Canon out := by
  have spec : absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut (fixed,two,eight,nodes,low,a) i
      ⦃ out => out.2=(fixed,two,eight,nodes,low,a) ∧ Canon out.1 ⦄ := by
    change (do let b ← FIx_Absorption.blockRun fixed two eight nodes i
               let w ← field.QM31.mul low b
               let q ← Array.index_usize a i
               let out ← field.QM31.mul w q
               ok (out,(fixed,two,eight,nodes,low,a)))
      ⦃ out => out.2=(fixed,two,eight,nodes,low,a) ∧ Canon out.1 ⦄
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
