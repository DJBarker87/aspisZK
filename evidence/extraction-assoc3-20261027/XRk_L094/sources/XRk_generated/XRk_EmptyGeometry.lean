import XRk_GeometryProjection
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRk_EmptyGeometry
def emptySlice : Slice U32 := ⟨[],by simp⟩
def emptyValues : alloc.vec.Vec aspis_core.field.M31 := ⟨[],by simp⟩
def emptyGeometry (start : Usize) : verifier.QueryGeometry :=
  {start, inverses := ⟨[],by simp⟩, line_z := emptyValues}
/- Actual emitted empty-loop success. This witnesses a local accepted geometry
   branch; it is not the ten-query TX1 domain or joint top non-vacuity. -/
theorem run (start : Usize) :
    verifier.QueryGeometry.for_range_loop0 ⟨emptySlice,0⟩ start emptyValues emptyValues =
      ok (.Ok (emptyGeometry start)) := by
  unfold verifier.QueryGeometry.for_range_loop0
  rw [loop]
  simp [verifier.QueryGeometry.for_range_loop0.body,emptySlice,emptyValues,
    core.slice.iter.IteratorSliceIter.next,Slice.len,alloc.vec.Vec.is_empty,
    bind_tc_ok,emptyGeometry,UScalar.ofNatCore,UScalar.val,alloc.vec.Vec.new]
#print axioms run
end XRk_EmptyGeometry
