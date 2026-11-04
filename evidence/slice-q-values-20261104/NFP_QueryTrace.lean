import NFP_DotCaller
import NFP_ReturnCuts
import NFI_TraceResult
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_QueryTrace
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts
open Port3_NativeQueryBody
abbrev Inverse := Array U32 5#usize
inductive Event where
 | opening (proof : Slice U8) (i : Usize)
 | dots (q : Slice U8) (g : Array E 29#usize)
 | trace (tag : U16) (i : Usize) (value : E)
 | geometry (receiver : verifier.QueryGeometry) (i : Usize)
 | circle (alpha : E) (values : Dots) (inverse : Inverse)
 | fields (q : Slice U8)
 | line (alpha : E) (values : Dots) (inverse : Inverse)
 | product (a b : U32)
 | double (a : U32)
 | one
 | subtract (a b : U32)
 | accumulate (p : verifier.Prepared) (a : verifier.Accumulator) (node : U32)
   (value : E) (pending : verifier.BatchedWeights)
abbrev M := NFI_TraceResult.M Event
def eval {T : Type} (r : Result T) : M T := NFI_TraceResult.lift r
def mark (e : Event) : M Unit := NFI_TraceResult.mark e

def run (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) : M Out := Id.run do
 let ops := NFP_ObserverErasure.erase base
 return (do
  let i ← eval (Array.index_usize p.queries a.next)
  let u ← eval (lift (UScalar.cast .Usize i))
  mark (.opening proof a.next)
  let q ← eval (ops.op11 proof a.next)
  mark (.dots q g)
  let dots ← eval (ops.op20 q g)
  let i1 ← eval (lift (Usize.wrapping_mul 4#usize a.next))
  let we ← eval (Array.index_usize dots 0#usize)
  mark (.trace 9#u16 i1 we)
  eval (ops.op15 9#u16 i1 we)
  let i2 ← eval (lift (Usize.wrapping_mul 4#usize a.next))
  let i3 ← eval (lift (Usize.wrapping_add i2 1#usize))
  let we1 ← eval (Array.index_usize dots 1#usize)
  mark (.trace 9#u16 i3 we1)
  eval (ops.op15 9#u16 i3 we1)
  let i4 ← eval (lift (Usize.wrapping_mul 4#usize a.next))
  let i5 ← eval (lift (Usize.wrapping_add i4 2#usize))
  let we2 ← eval (Array.index_usize dots 2#usize)
  mark (.trace 9#u16 i5 we2)
  eval (ops.op15 9#u16 i5 we2)
  let i6 ← eval (lift (Usize.wrapping_mul 4#usize a.next))
  let i7 ← eval (lift (Usize.wrapping_add i6 3#usize))
  let we3 ← eval (Array.index_usize dots 3#usize)
  mark (.trace 9#u16 i7 we3)
  eval (ops.op15 9#u16 i7 we3)
  mark (.geometry geometry a.next)
  let inverse ← eval (ops.op18 geometry a.next)
  let we4 ← eval (Array.index_usize p.alpha 0#usize)
  mark (.circle we4 dots inverse)
  let folded ← eval (ops.op17 we4 dots inverse)
  let i8 ← eval (lift (Usize.wrapping_mul 2#usize a.next))
  mark (.trace 10#u16 i8 folded)
  eval (ops.op15 10#u16 i8 folded)
  mark (.fields q)
  let values ← eval (ops.op0 4#usize
   (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact ops) q)
  let i9 ← eval (u % 4#usize)
  let we5 ← eval (Array.index_usize values i9)
  let bad ← eval (core.cmp.PartialEq.ne.trait_default ops.widePartialEq folded we5)
  if bad then pure (.Err verifier.Error.Query) else do
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
   pure (.Ok (a1,b1)))

/-- Full partial Result, state and source-ordered call trace share the exact
frozen cohort body. Phase hooks produce no trace event under deployed None. -/
theorem erased (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) :
 (run ops proof p a g geometry pending).result =
 verifier.candidate.query_values (NFP_ObserverErasure.erase ops) proof p a g none geometry pending := by
 simp only [run,eval,mark,NFI_TraceResult.erase_bind,NFI_TraceResult.erase_lift,
  NFI_TraceResult.erase_mark,NFI_TraceResult.erase_pure,bind_tc_ok,
  verifier.candidate.query_values] <;> rfl
#print axioms erased
end AspisR1.NFP_QueryTrace
end
