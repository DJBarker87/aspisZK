import BatchedWeightsFlushPrimitiveV2
import AspisR1BatchedWeightsExtraction.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BatchedWeightsFlushLaneV8
open AspisR1BatchedWeightsExtraction
abbrev U64 := UScalar UScalarTy.U64
abbrev Lane := Array U64 4#usize

/-- The literal four-coordinate flush block in generated `BatchedWeights.push`.
The vector lookup/update around this block is handled by its caller. -/
def flushLane (lane : Lane) : Result Lane := do
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
  ok (Array.make 4#usize [i8,i12,i16,i20])

theorem flushLane_success (lane : Lane) (x0 x1 x2 x3 : U64)
    (h0 : Array.index_usize lane 0#usize = .ok x0)
    (h1 : Array.index_usize lane 1#usize = .ok x1)
    (h2 : Array.index_usize lane 2#usize = .ok x2)
    (h3 : Array.index_usize lane 3#usize = .ok x3) :
    ∃ y0 y1 y2 y3 : U64,
      BatchedWeightsFlushPrimitiveV2.generatedFlush x0 = .ok y0 ∧
      BatchedWeightsFlushPrimitiveV2.generatedFlush x1 = .ok y1 ∧
      BatchedWeightsFlushPrimitiveV2.generatedFlush x2 = .ok y2 ∧
      BatchedWeightsFlushPrimitiveV2.generatedFlush x3 = .ok y3 ∧
      y0.val = AspisR1BatchedFoldSourceStep.fold x0.val ∧
      y1.val = AspisR1BatchedFoldSourceStep.fold x1.val ∧
      y2.val = AspisR1BatchedFoldSourceStep.fold x2.val ∧
      y3.val = AspisR1BatchedFoldSourceStep.fold x3.val ∧
      flushLane lane = .ok (Array.make 4#usize [y0,y1,y2,y3]) := by
  obtain ⟨y0, hy0, hv0⟩ := BatchedWeightsFlushPrimitiveV2.generatedFlush_success x0
  obtain ⟨y1, hy1, hv1⟩ := BatchedWeightsFlushPrimitiveV2.generatedFlush_success x1
  obtain ⟨y2, hy2, hv2⟩ := BatchedWeightsFlushPrimitiveV2.generatedFlush_success x2
  obtain ⟨y3, hy3, hv3⟩ := BatchedWeightsFlushPrimitiveV2.generatedFlush_success x3
  refine ⟨y0,y1,y2,y3,hy0,hy1,hy2,hy3,hv0,hv1,hv2,hv3,?_⟩
  simp only [flushLane, h0, h1, h2, h3]
  change (do
    let z0 ← BatchedWeightsFlushPrimitiveV2.generatedFlush x0
    let z1 ← BatchedWeightsFlushPrimitiveV2.generatedFlush x1
    let z2 ← BatchedWeightsFlushPrimitiveV2.generatedFlush x2
    let z3 ← BatchedWeightsFlushPrimitiveV2.generatedFlush x3
    ok (Array.make 4#usize [z0,z1,z2,z3])) =
      .ok (Array.make 4#usize [y0,y1,y2,y3])
  simp only [hy0, hy1, hy2, hy3, bind_tc_ok]

#print axioms flushLane_success

theorem make_read0 (x y z w : U64) :
    Array.index_usize (Array.make 4#usize [x,y,z,w]) 0#usize = .ok x := by
  simp [Array.index_usize, Array.make]

theorem make_read1 (x y z w : U64) :
    Array.index_usize (Array.make 4#usize [x,y,z,w]) 1#usize = .ok y := by
  simp [Array.index_usize, Array.make]

theorem make_read2 (x y z w : U64) :
    Array.index_usize (Array.make 4#usize [x,y,z,w]) 2#usize = .ok z := by
  simp [Array.index_usize, Array.make]

theorem make_read3 (x y z w : U64) :
    Array.index_usize (Array.make 4#usize [x,y,z,w]) 3#usize = .ok w := by
  simp [Array.index_usize, Array.make]

theorem flushLane_coordinates (lane : Lane) (x0 x1 x2 x3 : U64)
    (h0 : Array.index_usize lane 0#usize = .ok x0)
    (h1 : Array.index_usize lane 1#usize = .ok x1)
    (h2 : Array.index_usize lane 2#usize = .ok x2)
    (h3 : Array.index_usize lane 3#usize = .ok x3) :
    ∃ out : Lane, ∃ y0 y1 y2 y3 : U64,
      flushLane lane = .ok out ∧
      BatchedWeightsFlushPrimitiveV2.generatedFlush x0 = .ok y0 ∧
      BatchedWeightsFlushPrimitiveV2.generatedFlush x1 = .ok y1 ∧
      BatchedWeightsFlushPrimitiveV2.generatedFlush x2 = .ok y2 ∧
      BatchedWeightsFlushPrimitiveV2.generatedFlush x3 = .ok y3 ∧
      Array.index_usize out 0#usize = .ok y0 ∧
      Array.index_usize out 1#usize = .ok y1 ∧
      Array.index_usize out 2#usize = .ok y2 ∧
      Array.index_usize out 3#usize = .ok y3 ∧
      y0.val = AspisR1BatchedFoldSourceStep.fold x0.val ∧
      y1.val = AspisR1BatchedFoldSourceStep.fold x1.val ∧
      y2.val = AspisR1BatchedFoldSourceStep.fold x2.val ∧
      y3.val = AspisR1BatchedFoldSourceStep.fold x3.val := by
  obtain ⟨y0,y1,y2,y3,hy0,hy1,hy2,hy3,hv0,hv1,hv2,hv3,hflush⟩ :=
    flushLane_success lane x0 x1 x2 x3 h0 h1 h2 h3
  refine ⟨Array.make 4#usize [y0,y1,y2,y3], y0,y1,y2,y3,hflush,
    hy0,hy1,hy2,hy3,?_,?_,?_,?_,hv0,hv1,hv2,hv3⟩
  · exact make_read0 y0 y1 y2 y3
  · exact make_read1 y0 y1 y2 y3
  · exact make_read2 y0 y1 y2 y3
  · exact make_read3 y0 y1 y2 y3
end BatchedWeightsFlushLaneV8
