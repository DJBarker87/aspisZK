import S4AllFourHeadDecodingV1
import S4AllFourHeadTailWitnessV1
import S4AllFourHeadResidueJoinV1
import S4HeadDecodeV1
import S4HeadAlignmentRootV1
import S4TailLiteralProductsRootV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1FastDotsAllFourCallbackHeadTailDecodeV1

abbrev Ops := AspisR1FastDotsAllFourHeadDecodingV1.Ops
abbrev Wide := AspisR1FastDotsAllFourHeadDecodingV1.Wide
abbrev Contribution := AspisR1FastDotsOuterFoldTraceV2.Contribution
abbrev ExactTrace := AspisR1FastDotsOuterFoldTraceV2.ExactTrace
abbrev CallbackWitness := AspisR1FastDotsAllFourHeadTailWitnessV1.CallbackWitness

def CallbackDecodedTrace (base ops : Ops) (a : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) (value : Wide) : Prop :=
    ∃ ds : List (List Contribution), ∃ starts : List Nat,
    ∃ limbs : Array Std.U64 8#usize,
    ∃ body : Wide, ∃ tailValue : Wide, ∃ wide28 : Wide,
    ∃ q : AspisR1EbyKPushDotBackend.PushQm,
    ∃ tailStart tail2 : AspisR1EbyKPushDotBackend.PushState,
    ∃ cs : List AspisR1FastDotsActualTailBodyTraceRootV1.Contribution,
      CallbackWitness ops a g slot value ∧
      ExactTrace (AspisR1FastDotsConcreteTailInstallRootV1.install base) a g slot
        AspisR1FastDotsStepSchedule.startBy (Array.repeat 8#usize 0#u64) limbs ds starts ∧
      ds.length = 7 ∧
      AspisR1FastDotsHeadTailSharedWitnessRootV2.FirstQueryInput ops a slot q ∧
      Array.index_usize g 28#usize = .ok wide28 ∧
      AspisR1FastDotsActualTailLoopTraceRootV1.RunTrace
        ops a g slot { start := 0#usize, «end» := 2#usize } tailStart tail2 cs ∧
      ops.ebyKFinish tail2 = .ok tailValue ∧
      AspisR1DotCountBoundV1.AcceptedPushTrace
        AspisR1FastDotsPushProductTraceRootV1.raw EbyKNewToPushStateABI.pushZero
        ((wide28,q)::cs.map (fun c => (c.coefficient,c.scalar))) tail2 ∧
      AspisR1FastDotsPushProductTraceRootV1.stateValue tail2 =
        ((wide28,q)::cs.map (fun c => (c.coefficient,c.scalar))).foldl
          AspisR1FastDotsPushProductTraceRootV1.addProduct
          (AspisR1FastDotsPushProductTraceRootV1.stateValue EbyKNewToPushStateABI.pushZero) ∧
      (AspisR1FastDotsTailFinishSourceMapV1.currentFinishWords tailValue).map
          (fun w => w.val) =
        ((tail2.c0.sums.val ++ tail2.c1.sums.val).map
          (fun x => x.val % AspisV8R17.RawReducer.P)) ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE value) =
        AspisR1FastDotsAllFourHeadResidueJoinV1.decodedBatchResidues ds +
        (((wide28,q)::cs.map (fun c => (c.coefficient,c.scalar))).map
          (fun p => AspisR1FastDotsTailFieldProductRootV1.wideDecoded p.1 *
            AspisR1FastDotsTailLiteralProductsRootV1.embedQM p.2)).sum

/-- The same successful callback yields its actual head batch trace and tail
    push trace, with the returned value decoded as the exact source head
    residues plus the literal ordered tail product sum. -/
theorem callback_value_decode_head_tail
    (base : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (value : Wide)
    (hc : CallbackWitness
      (AspisR1FastDotsConcreteTailInstallRootV1.install
        (AspisR1FastDotsAllFourHeadTailWitnessV1.outerOps base)) a g slot value)
    (hh : AspisR1FastDotsAllFourHeadDecodingV1.SlotHeadWitness base a g slot value) :
    CallbackDecodedTrace
      base
      (AspisR1FastDotsConcreteTailInstallRootV1.install
        (AspisR1FastDotsAllFourHeadTailWitnessV1.outerOps base)) a g slot value := by
  have hcKeep := hc
  rcases hc with ⟨iterT,limbsT,bodyT,valsT,wide28,q,tailStart,tail2,
      tailValue,cs,hstepT,hbaseT,harrayT,hwide28,hfirstQuery,hpackT,
      _hnew,hpush,hrun,hfinish,hadd,_htermIndices,_htermLength,
      haccepted,hproduct,_hcanonical,hdecodedAdd,hfinishWords⟩
  rcases hh with ⟨iterH,limbsH,valsH,bodyH,ds,starts,hstepH,hbaseH,
      harrayH,hbodySome,htrace,hseven,hmap,_hcanonicalH,hpackCoordinates⟩
  have htailCore : AspisR1FastDotsHeadChainUniqueRootV1.HeadCore
      (AspisR1FastDotsConcreteTailInstallRootV1.install
        (AspisR1FastDotsAllFourHeadTailWitnessV1.outerOps base))
      a g slot iterT limbsT valsT bodyT := ⟨hstepT,hbaseT,harrayT,hpackT⟩
  have hheadCore : AspisR1FastDotsHeadChainUniqueRootV1.HeadCore
      (AspisR1FastDotsCallbackHeadBatchCoordinatesV1.headOps
        (AspisR1FastDotsConcreteTailInstallRootV1.install base))
      a g slot iterH limbsH valsH bodyH := ⟨hstepH,hbaseH,harrayH,hbodySome⟩
  have halign := AspisR1FastDotsHeadAlignmentRootV1.source_heads_unique
      base a g slot iterT iterH limbsT limbsH valsT valsH bodyT bodyH
      htailCore hheadCore
  have hdecodeHead : AspisR1CurrentWide.Proof.decodeWide
      (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE bodyH) =
      AspisR1FastDotsAllFourHeadResidueJoinV1.decodedBatchResidues ds := by
    have hres := AspisR1FastDotsHeadDecodeV1.slot_packed_decode_matches_batch_residues
      valsH ds hmap
    have hresPublic : AspisR1FastDotsTailFieldProductRootV1.wideDecoded
        (AspisR1FastDotsN8WideFromLimbsABI.finishToCurrent
          (AspisR1EbyKFinish.Proof.wideFromParts
            (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word0 valsH)
            (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word1 valsH)
            (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word2 valsH)
            (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word3 valsH)
            (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word4 valsH)
            (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word5 valsH)
            (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word6 valsH)
            (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word7 valsH))) =
        AspisR1FastDotsAllFourHeadResidueJoinV1.decodedBatchResidues ds := hres
    rw [AspisR1FastDotsTailFieldProductRootV1.current_decode_eq,hpackCoordinates]
    exact hresPublic
  have htailDecode := AspisR1FastDotsTailLiteralProductsRootV1.finished_tail_eq_literal_sum
      tail2 tailValue ((wide28,q)::cs.map (fun c => (c.coefficient,c.scalar)))
      hproduct hfinishWords
  have hresult : AspisR1CurrentWide.Proof.decodeWide
      (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE value) =
      AspisR1FastDotsAllFourHeadResidueJoinV1.decodedBatchResidues ds +
        (((wide28,q)::cs.map (fun c => (c.coefficient,c.scalar))).map
          (fun p => AspisR1FastDotsTailFieldProductRootV1.wideDecoded p.1 *
            AspisR1FastDotsTailLiteralProductsRootV1.embedQM p.2)).sum := by
    calc
      _ = AspisR1CurrentWide.Proof.decodeWide
            (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE bodyT) +
          AspisR1CurrentWide.Proof.decodeWide
            (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE tailValue) := hdecodedAdd
      _ = _ := by rw [halign.2.2.2,hdecodeHead,htailDecode]
  exact ⟨ds,starts,limbsH,bodyT,tailValue,wide28,q,tailStart,tail2,cs,
    hcKeep,htrace,hseven,hfirstQuery,hwide28,hrun,hfinish,haccepted,hproduct,hfinishWords,hresult⟩

/-- One successful generated N=4 call retains four decoded head-plus-tail
    equations, each tied to its exact callback's source head and tail traces. -/
theorem generatedFourDotsN4_success_all_four_decoded_traces
    (base : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsHeadTailSharedWitnessRootV2.CoordBound
        (g.val[i.val]'(by simpa [g.property] using i.isLt)))
    {values : Array Wide 4#usize}
    (h : (AspisR1FastDotsAllFourHeadTailWitnessV1.outerOps base).arrayFromFn
      4#usize
      (AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (AspisR1FastDotsAllFourHeadTailWitnessV1.outerOps base)) (a,g) = .ok values) :
    ∃ v0 v1 v2 v3 : Wide, values.val = [v0,v1,v2,v3] ∧
      CallbackDecodedTrace
        base
        (AspisR1FastDotsConcreteTailInstallRootV1.install
          (AspisR1FastDotsAllFourHeadTailWitnessV1.outerOps base)) a g 0#usize v0 ∧
      CallbackDecodedTrace
        base
        (AspisR1FastDotsConcreteTailInstallRootV1.install
          (AspisR1FastDotsAllFourHeadTailWitnessV1.outerOps base)) a g 1#usize v1 ∧
      CallbackDecodedTrace
        base
        (AspisR1FastDotsConcreteTailInstallRootV1.install
          (AspisR1FastDotsAllFourHeadTailWitnessV1.outerOps base)) a g 2#usize v2 ∧
      CallbackDecodedTrace
        base
        (AspisR1FastDotsConcreteTailInstallRootV1.install
          (AspisR1FastDotsAllFourHeadTailWitnessV1.outerOps base)) a g 3#usize v3 := by
  obtain ⟨v0,v1,v2,v3,hvalues,hc0,hc1,hc2,hc3,hh0,hh1,hh2,hh3⟩ :=
    AspisR1FastDotsAllFourHeadDecodingV1.generatedFourDotsN4_success_all_four_head_decodings
      base a g hcoords h
  exact ⟨v0,v1,v2,v3,hvalues,
    callback_value_decode_head_tail base a g 0#usize v0 hc0 hh0,
    callback_value_decode_head_tail base a g 1#usize v1 hc1 hh1,
    callback_value_decode_head_tail base a g 2#usize v2 hc2 hh2,
    callback_value_decode_head_tail base a g 3#usize v3 hc3 hh3⟩

#print axioms callback_value_decode_head_tail
#print axioms generatedFourDotsN4_success_all_four_decoded_traces

end AspisR1FastDotsAllFourCallbackHeadTailDecodeV1
