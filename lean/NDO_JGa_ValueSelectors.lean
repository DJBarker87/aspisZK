import NDO_JGa_Map
import RPv_FIy_ValueSelector
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_ValueSelectors
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

theorem cell (s : pool_v1.pair_forest_copy_terminal.Selectors) (i : Usize) (hi : i.val<16)
    (hh : canonical s.high) (hl : canonical s.low) :
    ∃ q,FIy_ValueSelector.call s i=ok (q,s) ∧ Canon q := by
  have spec : FIy_ValueSelector.call s i ⦃ out => out.2=s ∧ Canon out.1 ⦄ := by
    unfold FIy_ValueSelector.call add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut VALUE_AUXILIARY_BLOCK
    step* <;> first | assumption | scalar_tac
  obtain ⟨⟨q,last⟩,call,same,hq⟩ := WP.spec_imp_exists spec
  exact ⟨q,same ▸ call,hq⟩
#print axioms cell

@[step] theorem source (s : pool_v1.pair_forest_copy_terminal.Selectors)
    (hh : canonical s.high) (hl : canonical s.low) :
    FIq_Native.core.array.Array.map FIy_ValueSelector.callback (Array.make 3#usize [0#usize,2#usize,4#usize]) s
      ⦃ out => canonical out ⦄ := by
  apply exists_imp_spec
  apply JGa_Map.source
  intro i hi
  have bound : i.val<16 := by
    simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl <;> decide
  exact cell s i bound hh hl
#print axioms source
end AspisR1.JGa_ValueSelectors
end
