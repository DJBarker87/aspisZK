import S4FirstFoldOpeningGeometryV1
set_option autoImplicit false
namespace AspisR1.S4LocalBatchModelTransportV1
open AspisR1.MixedLeafDecoder AspisR1.MixedLeafEncoding AspisR1.ExactLeafFieldCodec
open AspisV8R19.DuplexFrames

theorem local_batch_is_model_first_fold_input {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (packed1 packed2 : Fin 262144 → Option Bytes) (u : Fin 262144) (slot : Fin 4)
    (bs : Bytes) (c1 : MixedLeafEncoding.C1) (c2 : MixedLeafEncoding.C2) (gamma : E)
    (hp1 : packed1 u = some (bs.take 480))
    (hp2 : packed2 u = some (bs.drop 480))
    (hd1 : decodeC1 (bs.take 480) = some c1)
    (hd2 : decodeC2 (bs.drop 480) = some c2) :
    AspisV6Width29CorrelatedAgreement.width29Batch
      (fun lane => LiteralTypedWords.word eM eK (fun _ => c1 slot)
        (fun _ => c2 slot) lane (0 : Fin 1048576)) gamma =
      FirstFold.fibre (TwoFoldExtraction.batchedWord
        (TypedRecoveredWords.word eM eK packed1 packed2) gamma) u slot := by
  have hword : (fun lane => LiteralTypedWords.word eM eK (fun _ => c1 slot)
      (fun _ => c2 slot) lane (0 : Fin 1048576)) =
      (fun lane => FirstFold.fibre (TypedRecoveredWords.word eM eK packed1 packed2 lane) u slot) := by
    funext lane
    exact (S4FirstFoldOpeningGeometryV1.decoded_opening_first_fold_inputs
      eM eK packed1 packed2 u slot bs c1 c2 hp1 hp2 hd1 hd2 lane).symm
  rw [hword]
  exact S4FirstFoldOpeningGeometryV1.batch_value_is_first_fold_fibre
    (TypedRecoveredWords.word eM eK packed1 packed2) gamma u slot

theorem four_slot_local_batches_are_model_inputs {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (packed1 packed2 : Fin 262144 → Option Bytes) (u : Fin 262144)
    (bs : Bytes) (c1 : MixedLeafEncoding.C1) (c2 : MixedLeafEncoding.C2) (gamma : E)
    (hp1 : packed1 u = some (bs.take 480))
    (hp2 : packed2 u = some (bs.drop 480))
    (hd1 : decodeC1 (bs.take 480) = some c1)
    (hd2 : decodeC2 (bs.drop 480) = some c2) :
    List.ofFn (fun slot : Fin 4 => AspisV6Width29CorrelatedAgreement.width29Batch
      (fun lane => LiteralTypedWords.word eM eK (fun _ => c1 slot)
        (fun _ => c2 slot) lane (0 : Fin 1048576)) gamma) =
      List.ofFn (fun slot : Fin 4 => FirstFold.fibre (TwoFoldExtraction.batchedWord
        (TypedRecoveredWords.word eM eK packed1 packed2) gamma) u slot) := by
  apply congrArg List.ofFn
  funext slot
  exact local_batch_is_model_first_fold_input eM eK packed1 packed2 u slot bs c1 c2 gamma hp1 hp2 hd1 hd2
#print axioms local_batch_is_model_first_fold_input
#print axioms four_slot_local_batches_are_model_inputs
end AspisR1.S4LocalBatchModelTransportV1
