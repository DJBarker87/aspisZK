import F3U_Slice
import F3T_PublicExt
import F3T_ByteTag
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_SemanticBytes
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open F3T_ByteCarrier

theorem encoded {F C : Type} (c : DrvC_Installation.Configuration F C)
    (pub : Slice U8) (proof : Bytes) (v : Port1_Driver.Semantic)
    (decoded : Port1_Driver.decodeSemantic (DrvC_Installation.sdk c) pub=ok (some v))
    (encoded : alloc.vec.Vec U8)
    (serialized : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (AspisR1CurrentCaller.FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic v))=ok (.Ok encoded))
    (fit : 75+(bytesOf encoded.val).length≤SelectedTranscriptParams.L) :
    (input c ⟨bytesOf pub.val,proof⟩).semantic.value.pubBytes=bytesOf encoded.val := by
  change (semantic c ⟨bytesOf pub.val,proof⟩).pubBytes=_
  simp only [semantic,F3U_Slice.roundtrip,decoded,serialized,publicOf,dif_pos fit]

#print axioms encoded
end AspisR1.F3U_SemanticBytes
end
