import S9RegularKindExecutionV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9RegularTensorReadbackV1
open AspisR1S9ActualProcessKindTensorReachedV1
open AspisR1S9RegularKindExecutionV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- The SAME tensor slice is exactly the slice read by the subsequent dot.
This follows from the actual owned Vec borrow/back definitions and SAME
source execution; no allocator preservation or desired tensor meaning. -/
theorem execution_tensor_readback
    (self : weights.Weights) (kind : Usize) (f : Slice U8) (n : Usize)
    (ap0 ap1 : Powers) (scratch scratchOut : Scratch) (parts partsOut : Parts)
    (e : Execution self kind f n ap0 ap1 scratch scratchOut parts partsOut) :
    alloc.vec.Vec.deref scratchOut=e.tensorOut := by
  rw [e.scratchBack]
  have hb : (alloc.vec.Vec.deref_mut scratch).2=e.back := congrArg Prod.snd e.borrow
  rw [←hb]
  rfl

#print axioms execution_tensor_readback
end AspisR1S9RegularTensorReadbackV1
