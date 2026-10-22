import S4RecoveredOpeningWordV1
import R1TwoFoldExtraction
set_option autoImplicit false
namespace AspisR1.S4FirstFoldOpeningGeometryV1
open AspisR1.MixedLeafDecoder AspisR1.MixedLeafEncoding AspisR1.ExactLeafFieldCodec
open AspisR1.TypedRecoveredWords
open AspisV8R19.DuplexFrames
open AspisPool.AlgorithmicCircleDecoderV7

theorem queryLeaf_child (u : Fin 262144) (slot : Fin 4) :
    queryLeaf (AspisV5ComponentCConcreteFoldLinearity.childIndex u slot) = u := by
  apply Fin.ext
  change (4*u.val+slot.val)/4 = u.val
  have hs := slot.isLt
  omega

theorem querySlot_child (u : Fin 262144) (slot : Fin 4) :
    querySlot (AspisV5ComponentCConcreteFoldLinearity.childIndex u slot) = slot := by
  apply Fin.ext
  change (4*u.val+slot.val)%4 = slot.val
  have hs := slot.isLt
  omega

theorem decoded_opening_first_fold_inputs {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (packed1 packed2 : Fin 262144 → Option Bytes) (u : Fin 262144) (slot : Fin 4)
    (bs : Bytes) (c1 : MixedLeafEncoding.C1) (c2 : MixedLeafEncoding.C2)
    (hp1 : packed1 u = some (bs.take 480))
    (hp2 : packed2 u = some (bs.drop 480))
    (hd1 : decodeC1 (bs.take 480) = some c1)
    (hd2 : decodeC2 (bs.drop 480) = some c2) :
    ∀ lane, FirstFold.fibre (TypedRecoveredWords.word eM eK packed1 packed2 lane) u slot =
      LiteralTypedWords.word eM eK (fun _ => c1 slot) (fun _ => c2 slot) lane
        (AspisV5ComponentCConcreteFoldLinearity.childIndex u slot) := by
  have h1 : packed1 (queryLeaf (AspisV5ComponentCConcreteFoldLinearity.childIndex u slot)) =
      some (bs.take 480) := by simpa only [queryLeaf_child] using hp1
  have h2 : packed2 (queryLeaf (AspisV5ComponentCConcreteFoldLinearity.childIndex u slot)) =
      some (bs.drop 480) := by simpa only [queryLeaf_child] using hp2
  intro lane
  have hw := S4RecoveredOpeningWordV1.decoded_pair_matches_recovered_word
    eM eK packed1 packed2 (AspisV5ComponentCConcreteFoldLinearity.childIndex u slot)
    bs c1 c2 h1 h2 hd1 hd2 lane
  simpa only [FirstFold.fibre, querySlot_child] using hw

/-- The batching target is exactly the model's four first-fold input values;
this does not assert a fold equation or a source arithmetic refinement. -/
theorem batch_value_is_first_fold_fibre {E : Type} [Field E]
    (W : Fin 29 → InitialWord E) (gamma : E) (u : Fin 262144) (slot : Fin 4) :
    AspisV6Width29CorrelatedAgreement.width29Batch
      (fun lane => FirstFold.fibre (W lane) u slot) gamma =
      FirstFold.fibre (TwoFoldExtraction.batchedWord W gamma) u slot := by
  rfl
#print axioms queryLeaf_child
#print axioms querySlot_child
#print axioms decoded_opening_first_fold_inputs
#print axioms batch_value_is_first_fold_fibre
end AspisR1.S4FirstFoldOpeningGeometryV1
