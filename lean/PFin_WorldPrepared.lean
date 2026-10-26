import F3V_RunEvidence
import F3V_Install
import AuS1_Observe
import AuS1_Prepare
import F3R_PreparationInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_WorldPrepared
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem fields {F C : Type} (base : Configuration F C) (s : Submission) (H : Bytes → State)
    (e : Evidence (F3V_Install.configuration base) base.boundaries s H) :
    let c := F3V_Install.configuration base
    ∃ (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
      (data : RecordedBinaryExperimentBin.SourceInputs) (out : AspisR1PublicPreparation.verifier.Prepared)
      (v : LiteralOpeningView.View),
      let tr := LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2
      i.physical.bytes=MultiproofConeCanonical.bytesOf e.pub.val ∧ i.stored=MultiproofConeCanonical.bytesOf e.proof.val ∧
      OraclePortStoredParserC4.parseReached i.stored tr=some p ∧
      OraclePortSelectedDraft.queries tr=some q ∧ OraclePortStoredDecisionDraftC4.input p q tr=some data ∧
      Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared e.run.p) data.data q (SelectedChallengeMap.rhoOf data.rho) ∧
      AspisR1CurrentCaller.InstalledPreparation.currentPrepared out=e.run.p ∧
      LiteralOpeningView.read (OraclePortStoredDecisionDraftC4.typedRows p q tr)=some v ∧
      F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p data v)
        data.data (SelectedChallengeMap.rhoOf data.rho) q ∧
      SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H) (SdkD_PrepareLower.lower
        (SdkD_PrepareSource.code (Uni_Install.current c.currentBase c.reserved c.query c.geometry)
          c.boundaries c.std (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.proof ()
          (Array.repeat 29#usize e.run.zero))) []).2=
        (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).1 ∧
      OraclePortAdmission.Guard tr := by
  dsimp only
  let c := F3V_Install.configuration base
  obtain ⟨i,p,q,data,out,v,physical,stored,parser,queries,found,prepare,output,opening,prepared,preparationLog,guard⟩ := e.prepared
  rw [F3R_PreparationInstall.code] at preparationLog
  have lowered := AuS1_Observe.lower (F3U_Oracle.hashv H)
    (SdkD_PrepareSource.code (Uni_Install.current c.currentBase c.reserved c.query c.geometry)
      c.boundaries c.std (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.proof ()
        (Array.repeat 29#usize e.run.zero))
    (AuS1_Prepare.uniform _ _ _ _ (F3U_Oracle.hashv H) (fun _ _=>rfl) _ _ _ _) []
  simp only [SdkC_Source.readLog,List.filterMap_nil,List.nil_append] at lowered
  exact ⟨i,p,q,data,out,v,physical,stored,parser,queries,found,prepare,output,opening,prepared,
    lowered.trans preparationLog,guard⟩

#print axioms fields
end AspisR1.PFin_WorldPrepared
end
