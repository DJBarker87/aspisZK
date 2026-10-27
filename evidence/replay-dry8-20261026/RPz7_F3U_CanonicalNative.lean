import RPz7_F3U_SemanticBytes
import RPz7_F3T_HeadCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_CanonicalNative
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_ByteCarrier

theorem joined {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (H : Bytes → State) (pub : Slice U8) (stored : Bytes) (v : Port1_Driver.Semantic)
    (decoded : Port1_Driver.decodeSemantic (DrvC_Installation.sdk c) pub=ok (some v))
    (encoded : alloc.vec.Vec U8)
    (serialized : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (AspisR1CurrentCaller.FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic v))=ok (.Ok encoded))
    (i : F3_Model.Input) (sourceAccepted : (eval H (F3T_Installed.source c hashv (input c ⟨bytesOf pub.val,stored⟩))).2=true)
    (accepted : (eval H (F3_Model.verifier D i)).2=true)
    (logs : (eval H (F3T_Installed.source c hashv (input c ⟨bytesOf pub.val,stored⟩))).1=
      (eval H (F3_Model.verifier D i)).1)
    (physical : i.physical.bytes=bytesOf pub.val) (proof : i.stored=stored) (root : State)
    (head : (eval H (F3T_Installed.source c hashv (input c ⟨bytesOf pub.val,stored⟩))).1.head?=
      some (PublicInitFrame.frame (bytesOf encoded.val) root,H (PublicInitFrame.frame (bytesOf encoded.val) root))) :
    eval H (F3T_Installed.source c hashv (input c ⟨bytesOf pub.val,stored⟩))=
      eval H (F3_Model.verifier D (input c ⟨bytesOf pub.val,stored⟩)) := by
  have sem := F3T_SemanticHead.bytes D H i accepted (bytesOf encoded.val) root (by rw [←logs];exact head)
  have fits : 75+(bytesOf encoded.val).length≤SelectedTranscriptParams.L := by
    rw [←sem];exact i.semantic.value.initFits
  have canonical := F3U_SemanticBytes.encoded c pub stored v decoded encoded serialized fits
  have physicalEq : i.physical=(input c ⟨bytesOf pub.val,stored⟩).physical :=
    congrArg F3_Model.PhysicalPublic.mk physical
  exact F3T_HeadCanonical.source_eval c D H i ⟨bytesOf pub.val,stored⟩ _ sourceAccepted accepted logs
    physicalEq proof root (by rw [canonical];exact head)

#print axioms joined
end AspisR1.F3U_CanonicalNative
end
