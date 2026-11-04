import NGD_WrapFacts
import NCO_LoopSteps
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGD_SlotBoundaries
theorem step0 (slot : Usize) (h : 0#usize < slot) :
    NGD_SlotRef.slot_offset_loop.body slot 28359#usize 0#usize = ok (.cont (33031#usize,1#usize)) := by
  have m := NGD_WrapFacts.mul 32#usize 146#usize 4672#usize (by decide)
  have a := NGD_WrapFacts.add 28359#usize 4672#usize 33031#usize (by decide)
  have j := NGD_WrapFacts.add 0#usize 1#usize 1#usize (by decide)
  simp [NGD_SlotRef.slot_offset_loop.body, h, NGD_SlotRef.SLOT_NODES, Array.make, Array.index_usize, lift, Usize.wrapping_add, Usize.wrapping_mul, m, a, j]
#print axioms step0
theorem step1 (slot : Usize) (h : 1#usize < slot) :
    NGD_SlotRef.slot_offset_loop.body slot 33031#usize 1#usize = ok (.cont (37703#usize,2#usize)) := by
  have m := NGD_WrapFacts.mul 32#usize 146#usize 4672#usize (by decide)
  have a := NGD_WrapFacts.add 33031#usize 4672#usize 37703#usize (by decide)
  have j := NGD_WrapFacts.add 1#usize 1#usize 2#usize (by decide)
  simp [NGD_SlotRef.slot_offset_loop.body, h, NGD_SlotRef.SLOT_NODES, Array.make, Array.index_usize, lift, Usize.wrapping_add, Usize.wrapping_mul, m, a, j]
#print axioms step1
theorem step2 (slot : Usize) (h : 2#usize < slot) :
    NGD_SlotRef.slot_offset_loop.body slot 37703#usize 2#usize = ok (.cont (41799#usize,3#usize)) := by
  have m := NGD_WrapFacts.mul 32#usize 128#usize 4096#usize (by decide)
  have a := NGD_WrapFacts.add 37703#usize 4096#usize 41799#usize (by decide)
  have j := NGD_WrapFacts.add 2#usize 1#usize 3#usize (by decide)
  simp [NGD_SlotRef.slot_offset_loop.body, h, NGD_SlotRef.SLOT_NODES, Array.make, Array.index_usize, lift, Usize.wrapping_add, Usize.wrapping_mul, m, a, j]
#print axioms step2
theorem step3 (slot : Usize) (h : 3#usize < slot) :
    NGD_SlotRef.slot_offset_loop.body slot 41799#usize 3#usize = ok (.cont (47303#usize,4#usize)) := by
  have m := NGD_WrapFacts.mul 32#usize 172#usize 5504#usize (by decide)
  have a := NGD_WrapFacts.add 41799#usize 5504#usize 47303#usize (by decide)
  have j := NGD_WrapFacts.add 3#usize 1#usize 4#usize (by decide)
  simp [NGD_SlotRef.slot_offset_loop.body, h, NGD_SlotRef.SLOT_NODES, Array.make, Array.index_usize, lift, Usize.wrapping_add, Usize.wrapping_mul, m, a, j]
#print axioms step3
theorem step4 (slot : Usize) (h : 4#usize < slot) :
    NGD_SlotRef.slot_offset_loop.body slot 47303#usize 4#usize = ok (.cont (52807#usize,5#usize)) := by
  have m := NGD_WrapFacts.mul 32#usize 172#usize 5504#usize (by decide)
  have a := NGD_WrapFacts.add 47303#usize 5504#usize 52807#usize (by decide)
  have j := NGD_WrapFacts.add 4#usize 1#usize 5#usize (by decide)
  simp [NGD_SlotRef.slot_offset_loop.body, h, NGD_SlotRef.SLOT_NODES, Array.make, Array.index_usize, lift, Usize.wrapping_add, Usize.wrapping_mul, m, a, j]
#print axioms step4
theorem step5 (slot : Usize) (h : 5#usize < slot) :
    NGD_SlotRef.slot_offset_loop.body slot 52807#usize 5#usize = ok (.cont (57607#usize,6#usize)) := by
  have m := NGD_WrapFacts.mul 32#usize 150#usize 4800#usize (by decide)
  have a := NGD_WrapFacts.add 52807#usize 4800#usize 57607#usize (by decide)
  have j := NGD_WrapFacts.add 5#usize 1#usize 6#usize (by decide)
  simp [NGD_SlotRef.slot_offset_loop.body, h, NGD_SlotRef.SLOT_NODES, Array.make, Array.index_usize, lift, Usize.wrapping_add, Usize.wrapping_mul, m, a, j]
#print axioms step5
theorem boundary0 : NGD_SlotRef.slot_offset 0#usize = ok 28359#usize := by
  unfold NGD_SlotRef.slot_offset NGD_SlotRef.OFF_NODES NGD_SlotRef.slot_offset_loop
  exact NCO_LoopSteps.loop_done _ (28359#usize,0#usize) 28359#usize (by simp [NGD_SlotRef.slot_offset_loop.body])
#print axioms boundary0
theorem boundary1 : NGD_SlotRef.slot_offset 1#usize = ok 33031#usize := by
  unfold NGD_SlotRef.slot_offset NGD_SlotRef.OFF_NODES NGD_SlotRef.slot_offset_loop
  rw [NCO_LoopSteps.loop_continue _ (28359#usize,0#usize) (33031#usize,1#usize) (step0 _ (by decide))]
  exact NCO_LoopSteps.loop_done _ (33031#usize,1#usize) 33031#usize (by simp [NGD_SlotRef.slot_offset_loop.body])
#print axioms boundary1
theorem boundary2 : NGD_SlotRef.slot_offset 2#usize = ok 37703#usize := by
  unfold NGD_SlotRef.slot_offset NGD_SlotRef.OFF_NODES NGD_SlotRef.slot_offset_loop
  rw [NCO_LoopSteps.loop_continue _ (28359#usize,0#usize) (33031#usize,1#usize) (step0 _ (by decide))]
  rw [NCO_LoopSteps.loop_continue _ (33031#usize,1#usize) (37703#usize,2#usize) (step1 _ (by decide))]
  exact NCO_LoopSteps.loop_done _ (37703#usize,2#usize) 37703#usize (by simp [NGD_SlotRef.slot_offset_loop.body])
#print axioms boundary2
theorem boundary3 : NGD_SlotRef.slot_offset 3#usize = ok 41799#usize := by
  unfold NGD_SlotRef.slot_offset NGD_SlotRef.OFF_NODES NGD_SlotRef.slot_offset_loop
  rw [NCO_LoopSteps.loop_continue _ (28359#usize,0#usize) (33031#usize,1#usize) (step0 _ (by decide))]
  rw [NCO_LoopSteps.loop_continue _ (33031#usize,1#usize) (37703#usize,2#usize) (step1 _ (by decide))]
  rw [NCO_LoopSteps.loop_continue _ (37703#usize,2#usize) (41799#usize,3#usize) (step2 _ (by decide))]
  exact NCO_LoopSteps.loop_done _ (41799#usize,3#usize) 41799#usize (by simp [NGD_SlotRef.slot_offset_loop.body])
#print axioms boundary3
theorem boundary4 : NGD_SlotRef.slot_offset 4#usize = ok 47303#usize := by
  unfold NGD_SlotRef.slot_offset NGD_SlotRef.OFF_NODES NGD_SlotRef.slot_offset_loop
  rw [NCO_LoopSteps.loop_continue _ (28359#usize,0#usize) (33031#usize,1#usize) (step0 _ (by decide))]
  rw [NCO_LoopSteps.loop_continue _ (33031#usize,1#usize) (37703#usize,2#usize) (step1 _ (by decide))]
  rw [NCO_LoopSteps.loop_continue _ (37703#usize,2#usize) (41799#usize,3#usize) (step2 _ (by decide))]
  rw [NCO_LoopSteps.loop_continue _ (41799#usize,3#usize) (47303#usize,4#usize) (step3 _ (by decide))]
  exact NCO_LoopSteps.loop_done _ (47303#usize,4#usize) 47303#usize (by simp [NGD_SlotRef.slot_offset_loop.body])
#print axioms boundary4
theorem boundary5 : NGD_SlotRef.slot_offset 5#usize = ok 52807#usize := by
  unfold NGD_SlotRef.slot_offset NGD_SlotRef.OFF_NODES NGD_SlotRef.slot_offset_loop
  rw [NCO_LoopSteps.loop_continue _ (28359#usize,0#usize) (33031#usize,1#usize) (step0 _ (by decide))]
  rw [NCO_LoopSteps.loop_continue _ (33031#usize,1#usize) (37703#usize,2#usize) (step1 _ (by decide))]
  rw [NCO_LoopSteps.loop_continue _ (37703#usize,2#usize) (41799#usize,3#usize) (step2 _ (by decide))]
  rw [NCO_LoopSteps.loop_continue _ (41799#usize,3#usize) (47303#usize,4#usize) (step3 _ (by decide))]
  rw [NCO_LoopSteps.loop_continue _ (47303#usize,4#usize) (52807#usize,5#usize) (step4 _ (by decide))]
  exact NCO_LoopSteps.loop_done _ (52807#usize,5#usize) 52807#usize (by simp [NGD_SlotRef.slot_offset_loop.body])
#print axioms boundary5
theorem boundary6 : NGD_SlotRef.slot_offset 6#usize = ok 57607#usize := by
  unfold NGD_SlotRef.slot_offset NGD_SlotRef.OFF_NODES NGD_SlotRef.slot_offset_loop
  rw [NCO_LoopSteps.loop_continue _ (28359#usize,0#usize) (33031#usize,1#usize) (step0 _ (by decide))]
  rw [NCO_LoopSteps.loop_continue _ (33031#usize,1#usize) (37703#usize,2#usize) (step1 _ (by decide))]
  rw [NCO_LoopSteps.loop_continue _ (37703#usize,2#usize) (41799#usize,3#usize) (step2 _ (by decide))]
  rw [NCO_LoopSteps.loop_continue _ (41799#usize,3#usize) (47303#usize,4#usize) (step3 _ (by decide))]
  rw [NCO_LoopSteps.loop_continue _ (47303#usize,4#usize) (52807#usize,5#usize) (step4 _ (by decide))]
  rw [NCO_LoopSteps.loop_continue _ (52807#usize,5#usize) (57607#usize,6#usize) (step5 _ (by decide))]
  exact NCO_LoopSteps.loop_done _ (57607#usize,6#usize) 57607#usize (by simp [NGD_SlotRef.slot_offset_loop.body])
#print axioms boundary6
end NGD_SlotBoundaries
