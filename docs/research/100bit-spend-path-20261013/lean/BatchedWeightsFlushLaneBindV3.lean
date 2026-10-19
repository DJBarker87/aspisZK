import BatchedWeightsFlushLaneV8
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BatchedWeightsFlushLaneBindV1
open BatchedWeightsFlushLaneV8
abbrev U64 := UScalar UScalarTy.U64
abbrev Lane := Array U64 4#usize

theorem flushLane_bind (lane : Lane) {β : Type}
    (k : Lane → Result β) :
    (do
      let i5 ← Array.index_usize lane 0#usize
      let i6 ← lift (i5 &&& 2147483647#u64)
      let i7 ← i5 >>> 31#i32
      let i8 ← i6 + i7
      let i9 ← Array.index_usize lane 1#usize
      let i10 ← lift (i9 &&& 2147483647#u64)
      let i11 ← i9 >>> 31#i32
      let i12 ← i10 + i11
      let i13 ← Array.index_usize lane 2#usize
      let i14 ← lift (i13 &&& 2147483647#u64)
      let i15 ← i13 >>> 31#i32
      let i16 ← i14 + i15
      let i17 ← Array.index_usize lane 3#usize
      let i18 ← lift (i17 &&& 2147483647#u64)
      let i19 ← i17 >>> 31#i32
      let i20 ← i18 + i19
      k (Array.make 4#usize [i8,i12,i16,i20])) = (do
       let out ← flushLane lane
       k out) := by
  simp only [flushLane, bind_assoc_eq, bind_tc_ok]

#print axioms flushLane_bind
end BatchedWeightsFlushLaneBindV1
