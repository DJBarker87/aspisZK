import RPz8_F3U_CanonicalNative
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_SemanticJoin
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_ByteCarrier

/-- Export the semantic identity used INSIDE the existing canonical join.
This is needed to identify the original account sampler's recovery frames. -/
theorem same {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (H : Bytes → State) (pub : Slice U8) (stored : Bytes)
    (v : Port1_Driver.Semantic)
    (decoded : Port1_Driver.decodeSemantic (DrvC_Installation.sdk c) pub = ok (some v))
    (encoded : alloc.vec.Vec U8)
    (serialized : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (AspisR1CurrentCaller.FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic v)) = ok (.Ok encoded))
    (i : F3_Model.Input) (accepted : (eval H (F3_Model.verifier D i)).2 = true)
    (root : State)
    (head : (eval H (F3_Model.verifier D i)).1.head? =
      some (PublicInitFrame.frame (bytesOf encoded.val) root,H (PublicInitFrame.frame (bytesOf encoded.val) root))) :
    i.semantic = (input c ⟨bytesOf pub.val,stored⟩).semantic := by
  have bytes := F3T_SemanticHead.bytes D H i accepted _ root head
  have fits : 75+(bytesOf encoded.val).length ≤ SelectedTranscriptParams.L := by
    rw [←bytes]
    exact i.semantic.value.initFits
  have canonical := F3U_SemanticBytes.encoded c pub stored v decoded encoded serialized fits
  apply F3T_PublicExt.semantic_ext
  · exact bytes.trans canonical.symm
  · exact (F3T_AcceptedParser.tag D H i accepted).trans (F3T_ByteTag.semantic_tag c _).symm

#print axioms same
end AspisR1.ARQ_SemanticJoin
end
