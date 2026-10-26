import PFin_FirstCode
import PFin_WorldRuns
import F3S_FirstPairLog
import F3V_FirstCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_WorldFirst
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem log {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : Submission)
    (H : Bytes → State) (e : Evidence c B s H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (first : AspisR1CurrentCaller.verifier.candidate.tx1
      (GExp_FirstCode.installed (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std)
      (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize () none=ok (.Ok e.saved)) :
    SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
      (GExp_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
        c.boundaries c.std hashv (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
        e.pub e.proof 10#usize) []).2 =
    SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H) (SdkD_PrepareLower.lower
      (SdkD_PrepareSource.code (Uni_Install.current c.currentBase c.reserved c.query c.geometry)
        c.boundaries c.std (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.proof ()
        (Array.repeat 29#usize e.run.zero))) []).2 ++
    (SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
      (SdkC_BatchSource.currentCode (F3U_Oracle.hashv H) e.proof e.run.p e.run.root) []).2 ++
    SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
      (GExp_FirstCode.writerCode e.run.p {e.run.out with weights:=⟨e.run.flushed.val,e.run.flushed.property⟩}
        e.proof e.pub) []).2) := by
  have success := (GExq_FirstSource.source (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
    c.boundaries c.std (F3U_Oracle.hashv H) (D1 c H) () (fun _ _=>rfl)
    (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize).trans first
  have constants := SdkD_FoldedCut.installed_constants
    (Uni_Install.current c.currentBase c.reserved c.query c.geometry) c.boundaries c.std
  rw [Uni_Install.compose_tx1] at constants
  have result := F3S_FirstPairLog.log c.currentBase c.reserved c.query c.geometry c.boundaries c.std
    (F3U_Oracle.hashv H) (D1 c H) () (fun _ _=>rfl) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
    e.pub e.proof 10#usize e.saved e.run (Tx1Q_Execution.actual_slots _ _ _ _ _ _) e.zero
    constants.1 constants.2 e.rootView e.rootRange e.rootCopy success
  rw [PFin_FirstCode.same,F3S_BatchDictionary.current] at result
  rw [F3V_FirstCode.same H _ _ _ hashv (currentDigest c)]
  exact result

#print axioms log
end AspisR1.PFin_WorldFirst
end
