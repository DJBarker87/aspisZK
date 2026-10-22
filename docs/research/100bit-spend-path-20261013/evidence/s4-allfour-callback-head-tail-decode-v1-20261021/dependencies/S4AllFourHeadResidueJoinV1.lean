import S4HeadDecodeV1
import S4HeadAlignmentRootV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1FastDotsAllFourHeadResidueJoinV1

abbrev Ops := AspisR1FastDotsAllFourHeadDecodingV1.Ops
abbrev Wide := AspisR1FastDotsAllFourHeadDecodingV1.Wide
abbrev Contribution := AspisR1FastDotsOuterFoldTraceV2.Contribution
abbrev TowerWide := AspisR1FastDotsTailFieldProductRootV1.TowerWide
abbrev M31 := AspisV8R15.ExactTowerBase.M31Exact

def batchResidue (ds : List (List Contribution)) (j : Fin 8) : M31 :=
  (AspisR1.FastDotFoldedBatches.fullSum
      (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds j) %
    AspisR1BatchedFoldArithmetic.modulus : M31)

def decodedBatchResidues (ds : List (List Contribution)) : TowerWide :=
  ⟨AspisV8R17.QM31WordTower.embedQ
      ((batchResidue ds ⟨0,by decide⟩,batchResidue ds ⟨1,by decide⟩),
       (batchResidue ds ⟨2,by decide⟩,batchResidue ds ⟨3,by decide⟩)),
   AspisV8R17.QM31WordTower.embedQ
      ((batchResidue ds ⟨4,by decide⟩,batchResidue ds ⟨5,by decide⟩),
       (batchResidue ds ⟨6,by decide⟩,batchResidue ds ⟨7,by decide⟩))⟩

/-- The full callback's packed body is aligned with the head-only batch witness
    by deterministic equality of the four actual source operations. -/
theorem callback_body_decodes_to_its_batch_residues
    (base : Ops) (a : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) (value witnessTag : Wide)
    (hc : AspisR1FastDotsAllFourHeadTailWitnessV1.CallbackWitness
      (AspisR1FastDotsConcreteTailInstallRootV1.install
        (AspisR1FastDotsAllFourHeadDecodingV1.Outer base)) a g slot value)
    (hh : AspisR1FastDotsAllFourHeadDecodingV1.SlotHeadWitness
      base a g slot witnessTag) :
    ∃ callbackBody : Wide, ∃ ds : List (List Contribution),
      ds.length = 7 ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE callbackBody) =
          decodedBatchResidues ds := by
  rcases hc with ⟨iterT,limbsT,bodyT,valsT,wide28,q,tailStart,tail2,
      tailValue,cs,hstepT,hbaseT,harrayT,_hwide28,_hfirstQuery,hpackT,
      _hnew,_hpush,_htail,_hfinish,_hadd,_htermIndices,_htermLength,
      _haccepted,_hproduct,_hcanonical,_hdecodedAdd,_hfinishWords⟩
  rcases hh with ⟨iterH,limbsH,valsH,bodyH,ds,starts,hstepH,hbaseH,
      harrayH,hpackH,htrace,hseven,hmap,hcanonicalH,hpackCoordinates⟩
  have htailCore : AspisR1FastDotsHeadChainUniqueRootV1.HeadCore
      (AspisR1FastDotsConcreteTailInstallRootV1.install
        (AspisR1FastDotsAllFourHeadDecodingV1.Outer base))
      a g slot iterT limbsT valsT bodyT := ⟨hstepT,hbaseT,harrayT,hpackT⟩
  have hheadCore : AspisR1FastDotsHeadChainUniqueRootV1.HeadCore
      (AspisR1FastDotsCallbackHeadBatchCoordinatesV1.headOps
        (AspisR1FastDotsConcreteTailInstallRootV1.install base))
      a g slot iterH limbsH valsH bodyH := ⟨hstepH,hbaseH,harrayH,hpackH⟩
  have halign := AspisR1FastDotsHeadAlignmentRootV1.source_heads_unique
      base a g slot iterT iterH limbsT limbsH valsT valsH bodyT bodyH
      htailCore hheadCore
  have hdecodeHead : AspisR1CurrentWide.Proof.decodeWide
      (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE bodyH) =
      decodedBatchResidues ds := by
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
        decodedBatchResidues ds := hres
    rw [AspisR1FastDotsTailFieldProductRootV1.current_decode_eq,hpackCoordinates]
    exact hresPublic
  refine ⟨bodyT,ds,hseven,?_⟩
  rw [halign.2.2.2]
  exact hdecodeHead

/-- One successful generated N=4 array execution gives four callback bodies
    decoded to the exact batch-residue traces of those same callbacks. -/
theorem generatedFourDotsN4_success_all_four_callback_body_residues
    (base : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsHeadTailSharedWitnessRootV2.CoordBound
        (g.val[i.val]'(by simpa [g.property] using i.isLt)))
    {values : Array Wide 4#usize}
    (h : (AspisR1FastDotsAllFourHeadDecodingV1.Outer base).arrayFromFn 4#usize
      (AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (AspisR1FastDotsAllFourHeadDecodingV1.Outer base)) (a,g) = .ok values) :
    ∃ v0 v1 v2 v3 body0 body1 body2 body3 : Wide,
      ∃ ds0 ds1 ds2 ds3 : List (List Contribution),
      values.val = [v0,v1,v2,v3] ∧
      AspisR1FastDotsAllFourHeadTailWitnessV1.CallbackWitness
        (AspisR1FastDotsConcreteTailInstallRootV1.install
          (AspisR1FastDotsAllFourHeadDecodingV1.Outer base)) a g 0#usize v0 ∧
      AspisR1FastDotsAllFourHeadTailWitnessV1.CallbackWitness
        (AspisR1FastDotsConcreteTailInstallRootV1.install
          (AspisR1FastDotsAllFourHeadDecodingV1.Outer base)) a g 1#usize v1 ∧
      AspisR1FastDotsAllFourHeadTailWitnessV1.CallbackWitness
        (AspisR1FastDotsConcreteTailInstallRootV1.install
          (AspisR1FastDotsAllFourHeadDecodingV1.Outer base)) a g 2#usize v2 ∧
      AspisR1FastDotsAllFourHeadTailWitnessV1.CallbackWitness
        (AspisR1FastDotsConcreteTailInstallRootV1.install
          (AspisR1FastDotsAllFourHeadDecodingV1.Outer base)) a g 3#usize v3 ∧
      ds0.length = 7 ∧ ds1.length = 7 ∧ ds2.length = 7 ∧ ds3.length = 7 ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE body0) = decodedBatchResidues ds0 ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE body1) = decodedBatchResidues ds1 ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE body2) = decodedBatchResidues ds2 ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE body3) = decodedBatchResidues ds3 := by
  obtain ⟨v0,v1,v2,v3,hvalues,hc0,hc1,hc2,hc3,hh0,hh1,hh2,hh3⟩ :=
    AspisR1FastDotsAllFourHeadDecodingV1.generatedFourDotsN4_success_all_four_head_decodings
      base a g hcoords h
  obtain ⟨body0,ds0,hlen0,hdecode0⟩ := callback_body_decodes_to_its_batch_residues
    base a g 0#usize v0 v0 hc0 hh0
  obtain ⟨body1,ds1,hlen1,hdecode1⟩ := callback_body_decodes_to_its_batch_residues
    base a g 1#usize v1 v1 hc1 hh1
  obtain ⟨body2,ds2,hlen2,hdecode2⟩ := callback_body_decodes_to_its_batch_residues
    base a g 2#usize v2 v2 hc2 hh2
  obtain ⟨body3,ds3,hlen3,hdecode3⟩ := callback_body_decodes_to_its_batch_residues
    base a g 3#usize v3 v3 hc3 hh3
  exact ⟨v0,v1,v2,v3,body0,body1,body2,body3,ds0,ds1,ds2,ds3,
    hvalues,hc0,hc1,hc2,hc3,hlen0,hlen1,hlen2,hlen3,
    hdecode0,hdecode1,hdecode2,hdecode3⟩

#print axioms callback_body_decodes_to_its_batch_residues
#print axioms generatedFourDotsN4_success_all_four_callback_body_residues

end AspisR1FastDotsAllFourHeadResidueJoinV1
