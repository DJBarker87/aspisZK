import S4FourSlotCurrentArraySemanticsV1
import S4LocalBatchModelTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S4CurrentArrayModelInputsV1
open AspisR1FastDotsLiteralCallbackValueRootV1
open AspisR1FastDotsForwardLiteralValueRootV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1.MixedLeafEncoding AspisR1.MixedLeafDecoder
open AspisV8R15.ExactTowerBase
abbrev Wide := AspisR1FastDotsLiteralHeadSumRootV1.Wide
abbrev TowerWide := AspisR1FastDotsTailFieldProductRootV1.TowerWide

theorem same_current_array_is_model_input
    (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (currentValues : Array Wide 4#usize) (v0 v1 v2 v3 : Wide)
    (hvalues : currentValues.val = [v0,v1,v2,v3])
    (gamma : TowerWide) (c1 : C1) (c2 : C2)
    (hbytes : a.val.map ExtractedRecordByteValue.rawByte = encodeC1 c1 ++ encodeC2 c2)
    (hpowers : ∀ j : Fin 29, AspisR1FastDotsTailFieldProductRootV1.wideDecoded
        (g.val[j.val]'(by scalar_tac)) = gamma ^ j.val)
    (hf0 : LiteralFieldResult (literalOps concreteOps) a g 0#usize v0)
    (hf1 : LiteralFieldResult (literalOps concreteOps) a g 1#usize v1)
    (hf2 : LiteralFieldResult (literalOps concreteOps) a g 2#usize v2)
    (hf3 : LiteralFieldResult (literalOps concreteOps) a g 3#usize v3)
    (packed1 packed2 : Fin 262144 → Option AspisV8R19.DuplexFrames.Bytes)
    (u : Fin 262144)
    (hp1 : packed1 u = some ((a.val.map ExtractedRecordByteValue.rawByte).take 480))
    (hp2 : packed2 u = some ((a.val.map ExtractedRecordByteValue.rawByte).drop 480))
    (hd1 : decodeC1 ((a.val.map ExtractedRecordByteValue.rawByte).take 480) = some c1)
    (hd2 : decodeC2 ((a.val.map ExtractedRecordByteValue.rawByte).drop 480) = some c2) :
    currentValues.val.map (fun x => AspisR1CurrentWide.Proof.decodeWide
      (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) =
      List.ofFn (fun slot : Fin 4 => FirstFold.fibre
        (TwoFoldExtraction.batchedWord (TypedRecoveredWords.word
          ExactBaseProjection.embed (algebraMap QM31Exact TowerWide) packed1 packed2)
          gamma) u slot) := by
  have hlocal := AspisR1S4FourSlotCurrentArraySemanticsV1.four_slot_values_are_first_fold_fibres
    a g currentValues v0 v1 v2 v3 hvalues gamma c1 c2 hbytes hpowers hf0 hf1 hf2 hf3
  have hmodel := S4LocalBatchModelTransportV1.four_slot_local_batches_are_model_inputs
    ExactBaseProjection.embed (algebraMap QM31Exact TowerWide) packed1 packed2 u
    (a.val.map ExtractedRecordByteValue.rawByte) c1 c2 gamma hp1 hp2 hd1 hd2
  exact hlocal.trans hmodel
#print axioms same_current_array_is_model_input
end AspisR1.S4CurrentArrayModelInputsV1
