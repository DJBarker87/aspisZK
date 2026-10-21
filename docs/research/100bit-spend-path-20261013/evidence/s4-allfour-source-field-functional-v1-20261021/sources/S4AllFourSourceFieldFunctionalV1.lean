import S4AllFourCallbackSourceCoverageV1
import S4CallbackFieldSumRootV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1FastDotsAllFourSourceFieldFunctionalV1

open AspisR1FastDotsAllFourCallbackSourceCoverageV1

/-- On one destructured callback trace, the same batch list has complete
source-byte meaning and ordered coverage, and the actual returned value is
its literal head product sum plus the literal tail product sum. -/
theorem callback_source_field_functional
    (base ops : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (value : Wide)
    (h : CallbackDecodedTrace base ops a g slot value) :
    ∃ ds : List (List Contribution), ∃ starts : List Nat,
    ∃ limbs : Array Std.U64 8#usize, ∃ body tailValue wide28 : Wide,
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
            AspisR1FastDotsTailLiteralProductsRootV1.embedQM p.2)).sum := by
  rcases h with ⟨ds,starts,limbs,body,tailValue,wide28,q,tailStart,tail2,cs,
    hcb,htrace,hlen,hfirst,hwide,hrun,hfinish,haccepted,hproduct,hwords,hdecode⟩
  have hstart : AspisR1FastDotsStepSchedule.startBy.iter.start.val = 0 := by
    norm_num [AspisR1FastDotsStepSchedule.startBy, AspisR1FastDotsStepSchedule.startRange]
  have hend : AspisR1FastDotsStepSchedule.startBy.iter.end.val = 26 := by
    norm_num [AspisR1FastDotsStepSchedule.startBy, AspisR1FastDotsStepSchedule.startRange]
  have hindices := exact_trace_flattened_term_indices htrace hend
  have hmeaning := exact_trace_source_meanings htrace
  have hhead := AspisR1FastDotsCallbackFieldSumRootV1.exact_head_residues_are_source_products htrace
  rw [hhead] at hdecode
  refine ⟨ds,starts,limbs,body,tailValue,wide28,q,tailStart,tail2,cs,
    hcb,htrace,hlen,?_,hmeaning,hfirst,hwide,hrun,haccepted,?_⟩
  · simpa [hstart] using hindices
  · exact hdecode

#print axioms callback_source_field_functional

end AspisR1FastDotsAllFourSourceFieldFunctionalV1
