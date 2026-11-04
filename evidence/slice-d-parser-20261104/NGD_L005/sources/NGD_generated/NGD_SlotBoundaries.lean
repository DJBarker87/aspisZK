import NGD_SlotRef.Funs
import NCO_LoopSteps
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGD_SlotBoundaries
theorem boundary0 : NGD_SlotRef.slot_offset 0#usize = ok 28359#usize := by
  change loop (fun (a,i) => NGD_SlotRef.slot_offset_loop.body 0#usize a i) (28359#usize,0#usize) = _
  exact NCO_LoopSteps.loop_done _ (28359#usize,0#usize) 28359#usize (by rfl)
#print axioms boundary0
theorem boundary1 : NGD_SlotRef.slot_offset 1#usize = ok 33031#usize := by
  change loop (fun (a,i) => NGD_SlotRef.slot_offset_loop.body 1#usize a i) (28359#usize,0#usize) = _
  rw [NCO_LoopSteps.loop_continue _ (28359#usize,0#usize) (33031#usize,1#usize) (by rfl)]
  exact NCO_LoopSteps.loop_done _ (33031#usize,1#usize) 33031#usize (by rfl)
#print axioms boundary1
theorem boundary2 : NGD_SlotRef.slot_offset 2#usize = ok 37703#usize := by
  change loop (fun (a,i) => NGD_SlotRef.slot_offset_loop.body 2#usize a i) (28359#usize,0#usize) = _
  rw [NCO_LoopSteps.loop_continue _ (28359#usize,0#usize) (33031#usize,1#usize) (by rfl)]
  rw [NCO_LoopSteps.loop_continue _ (33031#usize,1#usize) (37703#usize,2#usize) (by rfl)]
  exact NCO_LoopSteps.loop_done _ (37703#usize,2#usize) 37703#usize (by rfl)
#print axioms boundary2
theorem boundary3 : NGD_SlotRef.slot_offset 3#usize = ok 41799#usize := by
  change loop (fun (a,i) => NGD_SlotRef.slot_offset_loop.body 3#usize a i) (28359#usize,0#usize) = _
  rw [NCO_LoopSteps.loop_continue _ (28359#usize,0#usize) (33031#usize,1#usize) (by rfl)]
  rw [NCO_LoopSteps.loop_continue _ (33031#usize,1#usize) (37703#usize,2#usize) (by rfl)]
  rw [NCO_LoopSteps.loop_continue _ (37703#usize,2#usize) (41799#usize,3#usize) (by rfl)]
  exact NCO_LoopSteps.loop_done _ (41799#usize,3#usize) 41799#usize (by rfl)
#print axioms boundary3
theorem boundary4 : NGD_SlotRef.slot_offset 4#usize = ok 47303#usize := by
  change loop (fun (a,i) => NGD_SlotRef.slot_offset_loop.body 4#usize a i) (28359#usize,0#usize) = _
  rw [NCO_LoopSteps.loop_continue _ (28359#usize,0#usize) (33031#usize,1#usize) (by rfl)]
  rw [NCO_LoopSteps.loop_continue _ (33031#usize,1#usize) (37703#usize,2#usize) (by rfl)]
  rw [NCO_LoopSteps.loop_continue _ (37703#usize,2#usize) (41799#usize,3#usize) (by rfl)]
  rw [NCO_LoopSteps.loop_continue _ (41799#usize,3#usize) (47303#usize,4#usize) (by rfl)]
  exact NCO_LoopSteps.loop_done _ (47303#usize,4#usize) 47303#usize (by rfl)
#print axioms boundary4
theorem boundary5 : NGD_SlotRef.slot_offset 5#usize = ok 52807#usize := by
  change loop (fun (a,i) => NGD_SlotRef.slot_offset_loop.body 5#usize a i) (28359#usize,0#usize) = _
  rw [NCO_LoopSteps.loop_continue _ (28359#usize,0#usize) (33031#usize,1#usize) (by rfl)]
  rw [NCO_LoopSteps.loop_continue _ (33031#usize,1#usize) (37703#usize,2#usize) (by rfl)]
  rw [NCO_LoopSteps.loop_continue _ (37703#usize,2#usize) (41799#usize,3#usize) (by rfl)]
  rw [NCO_LoopSteps.loop_continue _ (41799#usize,3#usize) (47303#usize,4#usize) (by rfl)]
  rw [NCO_LoopSteps.loop_continue _ (47303#usize,4#usize) (52807#usize,5#usize) (by rfl)]
  exact NCO_LoopSteps.loop_done _ (52807#usize,5#usize) 52807#usize (by rfl)
#print axioms boundary5
theorem boundary6 : NGD_SlotRef.slot_offset 6#usize = ok 57607#usize := by
  change loop (fun (a,i) => NGD_SlotRef.slot_offset_loop.body 6#usize a i) (28359#usize,0#usize) = _
  rw [NCO_LoopSteps.loop_continue _ (28359#usize,0#usize) (33031#usize,1#usize) (by rfl)]
  rw [NCO_LoopSteps.loop_continue _ (33031#usize,1#usize) (37703#usize,2#usize) (by rfl)]
  rw [NCO_LoopSteps.loop_continue _ (37703#usize,2#usize) (41799#usize,3#usize) (by rfl)]
  rw [NCO_LoopSteps.loop_continue _ (41799#usize,3#usize) (47303#usize,4#usize) (by rfl)]
  rw [NCO_LoopSteps.loop_continue _ (47303#usize,4#usize) (52807#usize,5#usize) (by rfl)]
  rw [NCO_LoopSteps.loop_continue _ (52807#usize,5#usize) (57607#usize,6#usize) (by rfl)]
  exact NCO_LoopSteps.loop_done _ (57607#usize,6#usize) 57607#usize (by rfl)
#print axioms boundary6
end NGD_SlotBoundaries
