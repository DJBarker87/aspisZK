import JHl_JointSkeleton
import JHm_PreparedClaim
import JHm_NonVacuity
import JHk_PreparedScalarBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_JointSkeleton
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry JHe_CurrentWriterImage

/-- The32-byte claim field of the SAME actual returned preparation. -/
theorem claim_bytes (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch)) :
    (WAdm_SourceBody.put (prepared p).claim).map CheckpointBytes5Writer.u8=JFq_Claim.bytes := by
  change (WAdm_SourceBody.put (CheckpointBytes3Namespaces.toE (Tx1Q_Carriers.e p.claim))).map _=_
  rw [JHm_PreparedClaim.source p input scratch prepare]
  simp only [WAdm_SourceBody.put,WAdm_SourceWriter.map_bytes,CheckpointBytesE.rawBytes,
    JHk_PreparedScalarBytes.rawKBytes]
  rfl
#print axioms claim_bytes

theorem selected (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch)) :
    (WAdm_SourceBody.put (prepared p).claim).map CheckpointBytes5Writer.u8=
      (JFx_NativeBytes.checkpoint.val.drop 632).take 32 :=
  (claim_bytes p input scratch prepare).trans JFq_Claim.selected.symm
#print axioms selected

/-- Actual preparation witness for the identified claim bytes; not a complete
inhabitant of the headline's runtime/game hypotheses. -/
theorem inhabited : ∃ (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize),
    verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch) ∧
    (WAdm_SourceBody.put (prepared p).claim).map CheckpointBytes5Writer.u8=
      (JFx_NativeBytes.checkpoint.val.drop 632).take 32 := by
  obtain ⟨p,scratch,initial,out,pending,after,g,flushed,prepare,init,pend,geo,query,flush⟩ :=
    JHc_InstalledQuery.inhabited
  exact ⟨p,_,scratch,prepare,selected p _ scratch prepare⟩
#print axioms inhabited

/-- Typed target retained until the actual full saved-byte equality is proved. -/
def Accepted1SavedStatement : Prop := JHl_JointSkeleton.Accepted1SavedStatement
/-- Same world/SDK and explicit TX2 success; this remains a pending target. -/
def JointStatement : Prop := JHl_JointSkeleton.JointStatement

theorem accepted_statement_unchanged : Accepted1SavedStatement=JHl_JointSkeleton.Accepted1SavedStatement := rfl
#print axioms accepted_statement_unchanged

theorem joint_statement_unchanged : JointStatement=JHl_JointSkeleton.JointStatement := rfl
#print axioms joint_statement_unchanged
#print Accepted1SavedStatement
#print JointStatement
end AspisR1.JHm_JointSkeleton
end
