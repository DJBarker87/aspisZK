import NFP_TraceTypes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_TraceBack
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts NFP_TraceTypes
open Port3_NativeQueryBody

def run (base : Ops) (p : verifier.Prepared) (a : verifier.Accumulator) (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) (inverse : Inverse) (values : Dots) : M Out :=
 let ops := NFP_ObserverErasure.erase base
 do
  let we6 ← eval (Array.index_usize p.alpha 1#usize)
  mark (.line we6 values inverse)
  let folded1 ← eval (ops.op16 we6 values inverse)
  let i10 ← eval (lift (Usize.wrapping_mul 2#usize a.next))
  let i11 ← eval (lift (Usize.wrapping_add i10 1#usize))
  mark (.trace 10#u16 i11 folded1)
  eval (ops.op15 10#u16 i11 folded1)
  let i12 ← eval (lift (Usize.wrapping_sub a.next geometry.start))
  let z ← eval (alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) geometry.line_z i12)
  mark (.product z z)
  let product ← eval (ops.op7 z z)
  mark (.double product)
  let doubled ← eval (ops.op8 product)
  mark .one
  let one ← eval ops.op5
  mark (.subtract doubled one)
  let node ← eval (ops.op6 doubled one)
  mark (.accumulate p a node folded1 pending)
  let (a1,b1) ← eval (verifier.accumulate_batched_with_node ops p a node folded1 pending)
  eval (ops.op19 none (.Query a.next))
  pure (.Ok (a1,b1))

theorem erased (base : Ops) (p : verifier.Prepared) (a : verifier.Accumulator) (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) (inverse : Inverse) (values : Dots) :
 (run base p a geometry pending inverse values).result = NFP_SuffixCuts.back (NFP_ObserverErasure.erase base) p a geometry pending inverse values := by
 simp only [run,eval,mark,NFI_TraceResult.erase_bind,NFI_TraceResult.erase_lift,
  NFI_TraceResult.erase_mark,pure_result,bind_tc_ok,
  NFP_QueryCuts.head,NFP_SuffixCuts.front,NFP_SuffixCuts.back] <;> rfl
#print axioms erased
end AspisR1.NFP_TraceBack
end
