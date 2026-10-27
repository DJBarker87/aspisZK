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
  have lenzero : emptySlice.len.val=0 := by
    change (BitVec.ofNat UScalarTy.Usize.numBits 0).toNat=0
    simp only [BitVec.toNat_ofNat,Nat.zero_mod]
  have hnext : core.slice.iter.IteratorSliceIter.next (⟨emptySlice,0⟩ : core.slice.iter.Iter U32)=
      ok (none,(⟨emptySlice,0⟩ : core.slice.iter.Iter U32)) := by
    unfold core.slice.iter.IteratorSliceIter.next
    simp only [lenzero,Nat.lt_irrefl,↓reduceDIte]
  have hempty : alloc.vec.Vec.is_empty Global emptyValues=ok true := rfl
  have hbody : verifier.QueryGeometry.for_range_loop0.body start ⟨emptySlice,0⟩ emptyValues emptyValues=
      ok (ControlFlow.done (.Ok (emptyGeometry start))) := by
    unfold verifier.QueryGeometry.for_range_loop0.body
    rw [hnext,bind_tc_ok,hempty,bind_tc_ok]
    rfl
  unfold verifier.QueryGeometry.for_range_loop0
  rw [loop]
  simp only [hbody]
#print axioms run
end XRk_EmptyGeometry
