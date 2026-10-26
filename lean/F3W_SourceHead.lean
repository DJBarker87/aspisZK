import F3W_SourceLog
import F3U_FirstHead
import F3U_OracleHead
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3W_SourceHead
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem head {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence c B s H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (first : AspisR1CurrentCaller.verifier.candidate.tx1
      (GExp_FirstCode.installed (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
        c.boundaries c.std) (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
        e.pub e.proof 10#usize () none=ok (.Ok e.saved)) :
    ∃ (encoded : alloc.vec.Vec U8) (root : State),
      AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (AspisR1CurrentCaller.FirstComposition.toRetainedPublic
          (AspisS6CurrentVerifierCarrier.toPublic e.semantic))=ok (.Ok encoded) ∧
      (eval H (F3T_Installed.source c hashv (input c s))).1.head?=
        some (PublicInitFrame.frame (bytesOf encoded.val) root,H (PublicInitFrame.frame (bytesOf encoded.val) root)) := by
  have raw := (GExp_FirstSource.source
    (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std
    (F3U_Oracle.hashv H) (D1 c H) (fun _=>rfl)
    (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize).trans first
  rw [←F3U_FirstCode.same] at raw
  obtain ⟨encoded,root,state,serialized,firstHead⟩ := F3U_FirstHead.first _ c.boundaries c.std
    (F3U_Oracle.hashv H) (D1 c H) (fun _ _=>rfl)
    (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize () e.saved raw
  unfold RawK_CodeHead.head at firstHead
  rw [F3U_FirstCode.same] at firstHead
  rw [←F3V_FirstCode.same H _ _ _ hashv (currentDigest c)] at firstHead
  have whole := congrArg Prod.fst (F3W_SourceLog.evaluated c B s H e hashv first)
  have headPair : (eval H (F3T_Installed.source c hashv (input c s))).1.head?=
      some (PublicInitFrame.frame (bytesOf encoded.val) root,state) := by
    rw [whole]
    exact RawK_ModelHead.append_head _ _ _ firstHead
  have answer := F3U_OracleHead.answer _ H _ state headPair
  rw [answer] at headPair
  exact ⟨encoded,root,serialized,headPair⟩

#print axioms head
end AspisR1.F3W_SourceHead
end
