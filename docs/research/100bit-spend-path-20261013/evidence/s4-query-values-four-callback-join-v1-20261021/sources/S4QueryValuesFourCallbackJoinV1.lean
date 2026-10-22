import AspisR1QueryPrefixToCurrentFourDotsV1
import S4GeneratedFunctionFourCallbacksV2

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1FastDotsQueryValuesFourCallbackJoinV1

abbrev PrefixWide := AspisR1QueryPrefixToCurrentFourDotsV1.PrefixWide
abbrev CurrentWide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev CallbackDecodedTrace :=
  AspisR1FastDotsGeneratedFunctionFourCallbacksV2.CallbackDecodedTrace

def Outer (base : Ops) := AspisR1FastDotsAllFourHeadDecodingV1.Outer base

/-- A successful frozen-order query-values caller reaches the emitted `four_dots`
function on the same query slice and coordinate-mapped original coefficient array.
The generated function's successful Slice/TryFrom/unwrap path identifies its
N=608 callback input with the exact query prefix. Its four outputs remain linked
to the corresponding slot traces; opening and caller geometry remain explicit. -/
theorem query_values_success_four_callback_traces
    (openingOp : AspisR1QueryPrefixToCurrentFourDotsV1.PrefixOpeningOp)
    (base : Ops) (proof : Slice Std.U8)
    (p : AspisR1Stage2QueryTailCut.verifier.Prepared)
    (a : AspisR1Stage2QueryTailCut.verifier.Accumulator)
    (g : Array PrefixWide 29#usize)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsHeadTailSharedWitnessRootV2.CoordBound
        ((AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g).val[i.val]'(by simpa [AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent,
            g.property] using i.isLt)))
    (obs : Option (AspisR1Stage2QueryTailCut.verifier.Phase → Result Unit))
    (geometry : AspisR1Stage2QueryTailCut.verifier.QueryGeometry)
    (pending : AspisR1Stage2QueryTailCut.verifier.BatchedWeights)
    {out : core.result.Result
      (Std.Usize × Std.Usize × Slice Std.U8 × Array PrefixWide 4#usize)
      AspisR1Stage2QueryTailCut.verifier.Error}
    (h : AspisR1Stage2QueryTailCut.query_values_forward_prefix_ops
      openingOp
      (AspisR1QueryPrefixToCurrentFourDotsV1.currentFourDotsAsPrefix (Outer base))
      proof p a g obs geometry pending = .ok out) :
    ∃ (i : Std.U32) (u : Std.Usize) (q : Slice Std.U8)
      (dots : Array CurrentWide 4#usize)
      (arrayQ : Array Std.U8 608#usize)
      (v0 v1 v2 v3 : CurrentWide),
      Array.index_usize p.queries a.next = .ok i ∧
      lift (UScalar.cast .Usize i) = .ok u ∧
      openingOp proof a.next = .ok q ∧
      AspisR1FastDotsCurrent.fast_dots.four_dots (Outer base) q
        (AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g) = .ok dots ∧
      out = core.result.Result.Ok (a.next, u, q,
        AspisR1QueryPrefixToCurrentFourDotsV1.currentArrayToPrefix dots) ∧
      arrayQ.val = q.val.slice 0 (608#usize) ∧
      (Outer base).arrayFromFn 4#usize
        (AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
          (Outer base))
        (arrayQ, AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g) = .ok dots ∧
      dots.val = [v0,v1,v2,v3] ∧
      CallbackDecodedTrace base
        (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base))
        arrayQ (AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g)
        0#usize v0 ∧
      CallbackDecodedTrace base
        (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base))
        arrayQ (AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g)
        1#usize v1 ∧
      CallbackDecodedTrace base
        (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base))
        arrayQ (AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g)
        2#usize v2 ∧
      CallbackDecodedTrace base
        (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base))
        arrayQ (AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g)
        3#usize v3 := by
  obtain ⟨i,u,q,dots,hindex,hu,hopen,hfour,hout⟩ :=
    AspisR1QueryPrefixToCurrentFourDotsV1.query_values_forward_prefix_actual_s4
      openingOp (Outer base) proof p a g obs geometry pending out h
  obtain ⟨arrayQ,hprefixBytes,harray,tail⟩ :=
    AspisR1FastDotsGeneratedFunctionFourCallbacksV2.generated_four_dots_success_four_callback_traces
      base q (AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g)
      hcoords hfour
  rcases tail with ⟨v0,v1,v2,v3,hvals,h0,h1,h2,h3⟩
  exact ⟨i,u,q,dots,arrayQ,v0,v1,v2,v3,hindex,hu,hopen,hfour,hout,
    hprefixBytes,harray,hvals,h0,h1,h2,h3⟩

#print axioms query_values_success_four_callback_traces

end AspisR1FastDotsQueryValuesFourCallbackJoinV1
