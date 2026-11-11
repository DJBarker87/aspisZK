import RPz7_F3T_ByteCarrier
import RPz7_DrvC_Bytes
/-! PIN2 W9 (2026-11-11): STATEMENT CHANGE in the `serialized` premise only: the PIN2 serializer of `PreparationBinding.toPIN2 (toRetainedPublic (toPublic v))` (as F3T_ByteCarrier.semantic, F3W_SourceHead); conclusion and proof text unchanged. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Semantic
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames
open F3T_ByteCarrier MultiproofConeCanonical

theorem publicOf_bytes (b : Bytes) (fit : 75+b.length≤SelectedTranscriptParams.L) :
    (publicOf b).pubBytes=b := by simp only [publicOf,dif_pos fit]

theorem from_serialization {F C : Type} (c : DrvC_Installation.Configuration F C)
    (pub proof : Slice U8) (v : Port1_Driver.Semantic) (encoded : alloc.vec.Vec U8)
    (decode : Port1_Driver.decodeSemantic (DrvC_Installation.sdk c) pub=ok (some v))
    (serialized : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (AspisR1PublicPreparation.PreparationBinding.toPIN2 (AspisR1CurrentCaller.FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic v)))=
        ok (.Ok encoded))
    (fit : 75+(bytesOf encoded.val).length≤SelectedTranscriptParams.L) :
    (input c ⟨bytesOf pub.val,bytesOf proof.val⟩).semantic.value.pubBytes=bytesOf encoded.val ∧
      (input c ⟨bytesOf pub.val,bytesOf proof.val⟩).semantic.value.tag=2 := by
  simp only [input,semantic,DrvC_Bytes.asSlice,decode,serialized,publicOf,dif_pos fit]
  constructor <;> trivial

#print axioms publicOf_bytes
#print axioms from_serialization
end AspisR1.F3T_Semantic
end
