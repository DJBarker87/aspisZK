import PFin_WorldHead
import F3T_HeadCanonical
import F3U_SubmissionIdentity
import PFin_WorldEval
import PFin_FirstCode
import F3U_FirstHead
import F3U_OracleHead
import F3U_SemanticBytes
import PFin_WorldSource
import F3U_ReifyExact
import F3V_FirstCode
import F3V_SecondComplete
import GExp_SecondSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_WorldCanonical
open Aeneas Aeneas.Std Result CheckpointBytes5Effect MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem joined {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : Submission)
    (H : Bytes → State) (e : Evidence c B s H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (accepted : (eval H (F3T_Installed.source c hashv (input c s))).2=true)
    (first : AspisR1CurrentCaller.verifier.candidate.tx1
      (GExp_FirstCode.installed (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std)
      (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize () none=ok (.Ok e.saved))
    (decoder : LiteralByteProtocol.Decoder) (i : F3_Model.Input)
    (physical : i.physical.bytes=bytesOf e.pub.val) (stored : i.stored=bytesOf e.proof.val)
    (logs : (eval H (F3T_Installed.source c hashv (input c s))).1=(eval H (F3_Model.verifier decoder i)).1)
    (modelAccepted : (eval H (F3_Model.verifier decoder i)).2=true) :
    eval H (F3T_Installed.source c hashv (input c s))=eval H (F3_Model.verifier decoder (input c s)) := by
  obtain ⟨encoded,root,serialized,head⟩ := PFin_WorldHead.head c B s H e hashv accepted first
  have modelHead : (eval H (F3_Model.verifier decoder i)).1.head?=
      some (PublicInitFrame.frame (bytesOf encoded.val) root,H (PublicInitFrame.frame (bytesOf encoded.val) root)) := by
    rw [←logs]
    exact head
  have modelBytes := F3T_SemanticHead.bytes decoder H i modelAccepted _ root modelHead
  have fit : 75+(bytesOf encoded.val).length≤SelectedTranscriptParams.L := by
    rw [←modelBytes]
    exact i.semantic.value.initFits
  have canonicalBytes := F3U_SemanticBytes.encoded c e.pub (bytesOf e.proof.val) e.semantic e.decoded encoded serialized fit
  have submission : s=⟨bytesOf e.pub.val,bytesOf e.proof.val⟩ :=
    F3U_SubmissionIdentity.ext _ _ e.pubBytes.symm e.proofBytes.symm
  rw [←submission] at canonicalBytes
  have canonicalHead : (eval H (F3T_Installed.source c hashv (input c s))).1.head?=
      some (PublicInitFrame.frame (input c s).semantic.value.pubBytes root,
        H (PublicInitFrame.frame (input c s).semantic.value.pubBytes root)) := by
    rw [canonicalBytes]
    exact head
  have physicalEq : i.physical=(input c s).physical :=
    congrArg F3_Model.PhysicalPublic.mk (physical.trans e.pubBytes)
  exact F3T_HeadCanonical.source_eval c decoder H i s _ accepted modelAccepted logs physicalEq
    (stored.trans e.proofBytes) root canonicalHead

#print axioms joined
end AspisR1.PFin_WorldCanonical
end
