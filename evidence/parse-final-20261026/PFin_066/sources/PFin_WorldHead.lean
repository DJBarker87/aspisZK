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
namespace AspisR1.PFin_WorldHead
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem head {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : Submission)
    (H : Bytes → State) (e : Evidence c B s H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (accepted : (eval H (F3T_Installed.source c hashv (input c s))).2=true)
    (first : AspisR1CurrentCaller.verifier.candidate.tx1
      (GExp_FirstCode.installed (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std)
      (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize () none=ok (.Ok e.saved)) :
    ∃ (encoded : alloc.vec.Vec U8) (root : State),
      AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (AspisR1CurrentCaller.FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic e.semantic))=ok (.Ok encoded) ∧
      (eval H (F3T_Installed.source c hashv (input c s))).1.head?=
        some (PublicInitFrame.frame (bytesOf encoded.val) root,H (PublicInitFrame.frame (bytesOf encoded.val) root)) := by
  have success := (GExq_FirstSource.source (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
    c.boundaries c.std (F3U_Oracle.hashv H) (D1 c H) () (fun _ _=>rfl)
    (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize).trans first
  obtain ⟨encoded,root,state,serialized,firstHead⟩ := F3U_FirstHead.first
    (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std
    (F3U_Oracle.hashv H) (D1 c H) (fun _ _=>rfl) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
    e.pub e.proof 10#usize () e.saved success
  have pair := congrArg Prod.fst (PFin_WorldEval.log c B s H e hashv accepted first)
  dsimp only at pair
  rw [F3V_FirstCode.same H _ _ _ hashv (currentDigest c)] at pair
  rw [PFin_FirstCode.same] at firstHead
  unfold RawK_CodeHead.head at firstHead
  have sourceHead : (eval H (F3T_Installed.source c hashv (input c s))).1.head?=
      some (PublicInitFrame.frame (bytesOf encoded.val) root,state) := by
    rw [pair]
    exact RawK_ModelHead.append_head _ _ _ firstHead
  have answer := F3U_OracleHead.answer _ H _ state sourceHead
  rw [answer] at sourceHead
  exact ⟨encoded,root,serialized,sourceHead⟩

#print axioms head
end AspisR1.PFin_WorldHead
end
