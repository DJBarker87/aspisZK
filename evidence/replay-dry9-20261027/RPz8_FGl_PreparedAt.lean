import RPz8_F3V_RunEvidence
import RPz8_FGl_FinishLeaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGl_PreparedAt
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

/-- Binding of the finish owner's model operands to the SAME actual prepared
result. Contains no accepted model verdict, whole-source equality, or collision
association. Source generation and projection facts are retained explicitly. -/
def At {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : Submission) (H : Bytes → State)
    (e : Evidence c B s H) (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed)
    (q : Fin 22 → Fin 262144) (data : RecordedBinaryExperimentBin.SourceInputs) : Prop :=
  let tr := LiteralTranscript.erasePrefix (eval H
    (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2
  i.physical.bytes=bytesOf e.pub.val ∧ i.stored=bytesOf e.proof.val ∧
  OraclePortStoredParserC4.parseReached i.stored tr=some p ∧
  OraclePortSelectedDraft.queries tr=some q ∧ OraclePortStoredDecisionDraftC4.input p q tr=some data ∧
  Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared e.run.p) data.data q (SelectedChallengeMap.rhoOf data.rho) ∧
  ∃ (out : AspisR1PublicPreparation.verifier.Prepared) (v : LiteralOpeningView.View),
    AspisR1CurrentCaller.InstalledPreparation.currentPrepared out=e.run.p ∧
    LiteralOpeningView.read (OraclePortStoredDecisionDraftC4.typedRows p q tr)=some v ∧
    F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared
      (OraclePortAcceptedContextC6.context p data v) data.data (SelectedChallengeMap.rhoOf data.rho) q ∧
    AuS1_Recovery.log (Uni_Install.current c.currentBase c.reserved c.query c.geometry)
      c.boundaries c.std (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
      e.proof () (Array.repeat 29#usize e.run.zero)=
        (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).1 ∧
    OraclePortAdmission.Guard tr

/-- Five retained owner-law groups, with claim/alpha laws derived separately, on actual source finish primitives and
source-bound preparation operands. The ledger expands Holds into its five
atomic families; this definition gives no premise-count discount. -/
def Owners {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) : Prop :=
  ∀ (s : Submission) (H : Bytes → State) (e : Evidence c B s H)
    (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs) (t : Cons_Native.Witness),
    At c B s H e i p q data →
    Cons_Native.Calls (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.finish c.reserved c.query c.geometry
      (D2 c H) () e.pub e.proof e.saved.deref t →
    ∀ x : F3S_FinishWitness.Primitives c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2},
      FGl_FinishLeaves.Holds c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2} x q p
        (LiteralTranscript.erasePrefix (eval H
          (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2) data

end AspisR1.FGl_PreparedAt
end
