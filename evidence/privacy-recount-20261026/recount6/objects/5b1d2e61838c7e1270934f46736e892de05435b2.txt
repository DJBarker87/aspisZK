import R1Z.ProverRwFullExternalFuns
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_VectorShape
set_option autoImplicit false

/-- The safe reference tests length without inspecting, cloning or dropping T. -/
def emptyReference {T : Type} (v : alloc.vec.Vec T) : Result Bool :=
  ok (alloc.vec.Vec.len v == 0#usize)

/-- This identity is independent of the payload carrier. -/
theorem emptyReference_eq {T : Type} (v : alloc.vec.Vec T) :
    emptyReference v = ok (v.val.length == 0) := by
  classical
  have hz : alloc.vec.Vec.len v = 0#usize ↔ v.val.length = 0 := by
    scalar_tac
  unfold emptyReference
  apply congrArg Result.ok
  apply Bool.eq_iff_iff.mpr
  simpa only [beq_iff_eq] using hz
#print axioms emptyReference_eq
end R1Z.PV_CBL_VectorShape
