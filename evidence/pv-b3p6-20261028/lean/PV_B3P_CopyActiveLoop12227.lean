import PV_B3P_CopyActiveSource11227
import PV_B3P_PlanFold11227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227
set_option autoImplicit false

def active_step12 (selectors : reference_copy_terminal.Selectors)
    (sum : aspis_core.field.QM31) (block : Usize) : Result aspis_core.field.QM31 :=
  active_block_source11 selectors block sum

attribute [local irreducible] reference_copy_terminal.active_block227 active_block_source11

theorem active_body_binding12 (selectors : reference_copy_terminal.Selectors)
    (sum : aspis_core.field.QM31) (block : Usize) :
    reference_copy_terminal.Selectors.active_literal_loop.body selectors sum block =
      usize_body (active_step12 selectors) 64#usize (sum,block) := by
  unfold reference_copy_terminal.Selectors.active_literal_loop.body usize_body
  by_cases h : block < 64#usize
  · have hb : block.val < 64 := by scalar_tac
    simp only [h,if_pos,active_step12,active_block_source_binding11 selectors block sum hb]
  · simp only [h,if_neg]

theorem active_loop_binding12 (selectors : reference_copy_terminal.Selectors)
    (sum : aspis_core.field.QM31) (block : Usize) :
    reference_copy_terminal.Selectors.active_literal_loop selectors sum block =
      loop (usize_body (active_step12 selectors) 64#usize) (sum,block) := by
  unfold reference_copy_terminal.Selectors.active_literal_loop
  apply congrArg (fun body => loop body (sum,block))
  funext state
  exact active_body_binding12 selectors state.1 state.2

theorem active_literal_fold12 (selectors : reference_copy_terminal.Selectors) :
    reference_copy_terminal.Selectors.active_literal selectors =
      PV_B3P_Ordered227.fold (active_step12 selectors)
        (usize_indices11 64 0#usize) aspis_core.field.QM31.ZERO := by
  change reference_copy_terminal.Selectors.active_literal_loop selectors _ _ = _
  rw [active_loop_binding12]
  exact loop_as_fold11 _ 64#usize 0#usize 64 _ (by scalar_tac)

#print axioms active_body_binding12
#print axioms active_loop_binding12
#print axioms active_literal_fold12
end PV_B3P_Binding12227
