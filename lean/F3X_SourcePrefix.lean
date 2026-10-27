import F3W_SourceLog
import F3W_FirstLog
import AuS1_Observe
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_SourcePrefix
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem chronological {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : Submission) (H : Bytes → State)
    (e : Evidence c B s H) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (first : AspisR1CurrentCaller.verifier.candidate.tx1
      (GExp_FirstCode.installed (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
        c.boundaries c.std) (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
        e.pub e.proof 10#usize () none=ok (.Ok e.saved)) :
    ∃ tail,(eval H (F3T_Installed.source c hashv (input c s))).1=
      AuS1_Recovery.log (Uni_Install.current c.currentBase c.reserved c.query c.geometry)
        c.boundaries c.std (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
        e.proof () (Array.repeat 29#usize e.run.zero) ++ tail := by
  have whole := congrArg Prod.fst (F3W_SourceLog.evaluated c B s H e hashv first)
  simp only [Prod.fst] at whole
  rw [F3W_FirstLog.log c B s H e hashv first] at whole
  have lowered := AuS1_Observe.lower (F3U_Oracle.hashv H)
    (SdkD_PrepareSource.code (Uni_Install.current c.currentBase c.reserved c.query c.geometry)
      c.boundaries c.std (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
      e.proof () (Array.repeat 29#usize e.run.zero))
    (AuS1_Prepare.uniform _ _ _ _ (F3U_Oracle.hashv H) (fun _ _=>rfl) _ _ _ _) []
  rw [show SdkC_Source.readLog []=[] from rfl,List.nil_append] at lowered
  change _=AuS1_Recovery.log _ _ _ _ _ _ _ _ at lowered
  rw [lowered,List.append_assoc] at whole
  exact ⟨_,whole⟩

#print axioms chronological
end AspisR1.F3X_SourcePrefix
end
