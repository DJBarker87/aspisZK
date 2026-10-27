import F3V_Authenticated
import FGl_PreparedAt
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_RecoveryAt
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open DrvC_Installation F3V_RunEvidence
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
/-- Indexed folded recovery OR the existing collision, from the SAME original owner context. -/
theorem value {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : F3T_ByteCarrier.Submission)
    (H : Bytes → State) (e : Evidence c B s H) (i : F3_Model.Input)
    (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs)
    (atPrepared : FGl_PreparedAt.At c B s H e i p q data) (prior : Program Bytes State Unit) :
    let trace := (eval H prior).1 ++ AuS1_Recovery.log
      (Uni_Install.current c.currentBase c.reserved c.query c.geometry) c.boundaries c.std (D1 c H)
      (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.proof () (Array.repeat 29#usize e.run.zero)
    ∃ frame, FS2.Duplex.Read trace frame ∧
      BinRawByteCollisionTargets.pred 3 frame=some (OraclePortBatchDraft.committedRoot p 2) ∧
      (AuS1_Finish.Collision H trace p q ∨
        ∀ pos,pos<22 → OraclePortAllSelectedRecoveryC6.recovered trace frame p 2
          (OraclePortSelectedDraft.index q 2 pos)=some (OraclePortPackedChoiceC4.payload p 2 pos)) := by
  have parser := (OraclePortStoredParserC4.parsed i.stored _ p atPrepared.2.2.1).1
  rw [atPrepared.2.1] at parser
  obtain ⟨frame,read,target,recover⟩ := F3V_Authenticated.recovered c B s H e prior p parser
  exact ⟨frame,read,target,recover data.data (SelectedChallengeMap.rhoOf data.rho) q atPrepared.2.2.2.2.2.1⟩
#print axioms value
end AspisR1.FJo_RecoveryAt
end
