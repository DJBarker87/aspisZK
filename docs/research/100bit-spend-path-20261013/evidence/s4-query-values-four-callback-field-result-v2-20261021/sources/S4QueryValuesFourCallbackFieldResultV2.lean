import S4QueryValuesFourCallbackJoinV1
import S4AllFourSourceFieldFunctionalV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1FastDotsQueryValuesFourCallbackFieldResultV2

abbrev PrefixWide := AspisR1QueryPrefixToCurrentFourDotsV1.PrefixWide
abbrev CurrentWide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Outer := AspisR1FastDotsAllFourHeadDecodingV1.Outer
abbrev CallbackDecodedTrace := AspisR1FastDotsAllFourCallbackSourceCoverageV1.CallbackDecodedTrace
abbrev Contribution := AspisR1FastDotsAllFourCallbackSourceCoverageV1.Contribution
abbrev ExactTrace := AspisR1FastDotsAllFourCallbackSourceCoverageV1.ExactTrace
abbrev SourceMeaning := AspisR1FastDotsAllFourCallbackSourceCoverageV1.SourceMeaning

/-- Exact result proposition of the already checked per-callback source-field
functional. Keeping it opaque lets callers carry its full same-call existential
without case-splitting the decoded arithmetic witness. -/
def CallbackFieldResult (base ops : Ops) (a : Array Std.U8 608#usize)
    (g : Array CurrentWide 29#usize) (slot : Usize) (value : CurrentWide) : Prop :=
  ∃ ds : List (List Contribution), ∃ starts : List Nat,
  ∃ limbs : Array Std.U64 8#usize, ∃ body tailValue wide28 : CurrentWide,
  ∃ q : AspisR1EbyKPushDotBackend.PushQm,
  ∃ tailStart tail2 : AspisR1EbyKPushDotBackend.PushState,
  ∃ cs : List AspisR1FastDotsActualTailBodyTraceRootV1.Contribution,
    AspisR1FastDotsAllFourCallbackHeadTailDecodeV1.CallbackWitness ops a g slot value ∧
    ExactTrace (AspisR1FastDotsConcreteTailInstallRootV1.install base) a g slot
      AspisR1FastDotsStepSchedule.startBy (Array.repeat 8#usize 0#u64) limbs ds starts ∧
    ds.length = 7 ∧
    ds.flatten.map (fun c => c.term.val) = List.range' 0 26 ∧
    (∀ c ∈ ds.flatten, SourceMeaning a g slot c) ∧
    AspisR1FastDotsHeadTailSharedWitnessRootV2.FirstQueryInput ops a slot q ∧
    Array.index_usize g 28#usize = .ok wide28 ∧
    AspisR1FastDotsActualTailLoopTraceRootV1.RunTrace
      ops a g slot { start := 0#usize, «end» := 2#usize } tailStart tail2 cs ∧
    AspisR1DotCountBoundV1.AcceptedPushTrace
      AspisR1FastDotsPushProductTraceRootV1.raw EbyKNewToPushStateABI.pushZero
      ((wide28,q)::cs.map (fun c => (c.coefficient,c.scalar))) tail2 ∧
    AspisR1CurrentWide.Proof.decodeWide
      (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE value) =
    (ds.flatten.map AspisR1FastDotsHeadFieldAlgebraRootV1.sourceProduct).sum +
      (((wide28,q)::cs.map (fun c => (c.coefficient,c.scalar))).map
        (fun p => AspisR1FastDotsTailFieldProductRootV1.wideDecoded p.1 *
          AspisR1FastDotsTailLiteralProductsRootV1.embedQM p.2)).sum

theorem callback_field_result_of_trace
    (base ops : Ops) (a : Array Std.U8 608#usize) (g : Array CurrentWide 29#usize)
    (slot : Usize) (value : CurrentWide)
    (h : CallbackDecodedTrace base ops a g slot value) :
    CallbackFieldResult base ops a g slot value := by
  simpa only [CallbackFieldResult] using
    AspisR1FastDotsAllFourSourceFieldFunctionalV1.callback_source_field_functional
    base ops a g slot value h

theorem query_values_success_four_callback_field_results
    (openingOp : AspisR1QueryPrefixToCurrentFourDotsV1.PrefixOpeningOp)
    (base : Ops) (proof : Slice Std.U8)
    (p : AspisR1Stage2QueryTailCut.verifier.Prepared)
    (a : AspisR1Stage2QueryTailCut.verifier.Accumulator)
    (g : Array PrefixWide 29#usize)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsHeadTailSharedWitnessRootV2.CoordBound
        ((AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g).val[i.val]'(by
          simpa [AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent,
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
      dots.val = [v0,v1,v2,v3] ∧
      CallbackFieldResult base (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base))
        arrayQ (AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g) 0#usize v0 ∧
      CallbackFieldResult base (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base))
        arrayQ (AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g) 1#usize v1 ∧
      CallbackFieldResult base (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base))
        arrayQ (AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g) 2#usize v2 ∧
      CallbackFieldResult base (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base))
        arrayQ (AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g) 3#usize v3 := by
  obtain ⟨i,u,q,dots,arrayQ,v0,v1,v2,v3,hindex,hu,hopen,hfour,hout,
      hprefixBytes,harray,hvals,h0,h1,h2,h3⟩ :=
    AspisR1FastDotsQueryValuesFourCallbackJoinV1.query_values_success_four_callback_traces
      openingOp base proof p a g hcoords obs geometry pending h
  have hf0 := callback_field_result_of_trace base
    (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base)) arrayQ
    (AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g) 0#usize v0 h0
  have hf1 := callback_field_result_of_trace base
    (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base)) arrayQ
    (AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g) 1#usize v1 h1
  have hf2 := callback_field_result_of_trace base
    (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base)) arrayQ
    (AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g) 2#usize v2 h2
  have hf3 := callback_field_result_of_trace base
    (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base)) arrayQ
    (AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g) 3#usize v3 h3
  exact ⟨i,u,q,dots,arrayQ,v0,v1,v2,v3,hindex,hu,hopen,hfour,hout,
    hprefixBytes,hvals,hf0,hf1,hf2,hf3⟩

#print axioms callback_field_result_of_trace
#print axioms query_values_success_four_callback_field_results

end AspisR1FastDotsQueryValuesFourCallbackFieldResultV2
