import NFP_TraceTypes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_TraceFront
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts NFP_TraceTypes
open Port3_NativeQueryBody

def run (base : Ops) (p : verifier.Prepared) (a : verifier.Accumulator) (geometry : verifier.QueryGeometry) (u : Usize) (q : Slice U8) (dots : Dots) : M (Inverse × E × Dots × Bool) :=
 let ops := NFP_ObserverErasure.erase base
 do
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
  pure (inverse,folded,values,bad)

theorem erased (base : Ops) (p : verifier.Prepared) (a : verifier.Accumulator) (geometry : verifier.QueryGeometry) (u : Usize) (q : Slice U8) (dots : Dots) :
 (run base p a geometry u q dots).result = NFP_SuffixCuts.front (NFP_ObserverErasure.erase base) p a geometry u q dots := by
 simp only [run,eval,mark,NFI_TraceResult.erase_bind,NFI_TraceResult.erase_lift,
  NFI_TraceResult.erase_mark,pure_result,bind_tc_ok,
  NFP_QueryCuts.head,NFP_SuffixCuts.front,NFP_SuffixCuts.back] <;> rfl
#print axioms erased
end AspisR1.NFP_TraceFront
end
