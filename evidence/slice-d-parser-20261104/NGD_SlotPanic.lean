import NGD_SlotBoundaries
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGD_SlotPanic
theorem rejected (slot : Usize) (bad : 6 < slot.val) :
    NGD_SlotRef.slot_offset slot = fail .arrayOutOfBounds := by
  unfold NGD_SlotRef.slot_offset NGD_SlotRef.OFF_NODES NGD_SlotRef.slot_offset_loop
  rw [NCO_LoopSteps.loop_continue _ (28359#usize,0#usize) (33031#usize,1#usize) (NGD_SlotBoundaries.step0 _ (by scalar_tac))]
  rw [NCO_LoopSteps.loop_continue _ (33031#usize,1#usize) (37703#usize,2#usize) (NGD_SlotBoundaries.step1 _ (by scalar_tac))]
  rw [NCO_LoopSteps.loop_continue _ (37703#usize,2#usize) (41799#usize,3#usize) (NGD_SlotBoundaries.step2 _ (by scalar_tac))]
  rw [NCO_LoopSteps.loop_continue _ (41799#usize,3#usize) (47303#usize,4#usize) (NGD_SlotBoundaries.step3 _ (by scalar_tac))]
  rw [NCO_LoopSteps.loop_continue _ (47303#usize,4#usize) (52807#usize,5#usize) (NGD_SlotBoundaries.step4 _ (by scalar_tac))]
  rw [NCO_LoopSteps.loop_continue _ (52807#usize,5#usize) (57607#usize,6#usize) (NGD_SlotBoundaries.step5 _ (by scalar_tac))]
  have h : 6#usize < slot := by scalar_tac
  have step : NGD_SlotRef.slot_offset_loop.body slot 57607#usize 6#usize = fail .arrayOutOfBounds := by
    simp [NGD_SlotRef.slot_offset_loop.body, h, NGD_SlotRef.SLOT_NODES,
      Array.index_usize, Array.make]
  conv_lhs => unfold loop
  simp only [step]
#print axioms rejected
end NGD_SlotPanic
