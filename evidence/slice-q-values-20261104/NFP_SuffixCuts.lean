import NFP_QueryCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_SuffixCuts
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts
open Port3_NativeQueryBody
abbrev Inverse := Array aspis_core.field.M31 5#usize

def front (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (geometry : verifier.QueryGeometry) (u : Usize) (q : Slice U8) (dots : Dots) :
 Result (Inverse × E × Dots × Bool) := do
  let i1 ← lift (Std.Usize.wrapping_mul 4#usize a.next)
  let we ← Array.index_usize dots 0#usize
  ops.op15 9#u16 i1 we
  let i2 ← lift (Std.Usize.wrapping_mul 4#usize a.next)
  let i3 ← lift (Std.Usize.wrapping_add i2 1#usize)
  let we1 ← Array.index_usize dots 1#usize
  ops.op15 9#u16 i3 we1
  let i4 ← lift (Std.Usize.wrapping_mul 4#usize a.next)
  let i5 ← lift (Std.Usize.wrapping_add i4 2#usize)
  let we2 ← Array.index_usize dots 2#usize
  ops.op15 9#u16 i5 we2
  let i6 ← lift (Std.Usize.wrapping_mul 4#usize a.next)
  let i7 ← lift (Std.Usize.wrapping_add i6 3#usize)
  let we3 ← Array.index_usize dots 3#usize
  ops.op15 9#u16 i7 we3
  let inverse ← ops.op18 geometry a.next
  let we4 ← Array.index_usize p.alpha 0#usize
  let folded ← ops.op17 we4 dots inverse
  let i8 ← lift (Std.Usize.wrapping_mul 2#usize a.next)
  ops.op15 10#u16 i8 folded
  let values ←
    ops.op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact ops)
      q
  let i9 ← u % 4#usize
  let we5 ← Array.index_usize values i9
  let b ←
    core.cmp.PartialEq.ne.trait_default
      ops.widePartialEq
      folded we5
  ok (inverse,folded,values,b)

def back (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (inverse : Inverse) (values : Dots) : Result Out := do
    let we6 ← Array.index_usize p.alpha 1#usize
    let folded1 ← ops.op16 we6 values inverse
    let i10 ← lift (Std.Usize.wrapping_mul 2#usize a.next)
    let i11 ← lift (Std.Usize.wrapping_add i10 1#usize)
    ops.op15 10#u16 i11 folded1
    let i12 ← lift (Std.Usize.wrapping_sub a.next geometry.start)
    let z ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) geometry.line_z i12
    let m ← ops.op7 z z
    let m1 ← ops.op8 m
    let m2 ← ops.op5
    let node ← ops.op6 m1 m2
    let (a1, pending1) ←
      (verifier.accumulate_batched_with_node ops) p a node folded1 pending
    ops.op19 none (verifier.Phase.Query a.next)
    ok (core.result.Result.Ok (a1, pending1))

theorem source (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (u : Usize) (q : Slice U8) (dots : Dots) :
 tail ops p a geometry pending u q dots =
 (do let (inverse,_,values,b) ← front ops p a geometry u q dots
     if b then ok (.Err verifier.Error.Query)
     else back ops p a geometry pending inverse values) := by
 simp only [front,back,tail,bind_assoc_eq,bind_tc_ok] <;> rfl
#print axioms source
end AspisR1.NFP_SuffixCuts
end
