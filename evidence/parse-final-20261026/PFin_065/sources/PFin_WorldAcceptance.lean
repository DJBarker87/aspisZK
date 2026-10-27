import PFin_WorldJoin
import F3V_ModelAcceptance
import F3V_Checkpoint
import PFin_WorldSchedule
import PFin_WorldPrepared
import PFin_WorldCheckpoint
import PFin_WorldBatches
import F3V_Ten
import F3N_TenInput
import F3S_ModelLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_WorldAcceptance
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem values {F C : Type} (base : Configuration F C) (s : Submission) (H : Bytes → State)
    (e : Evidence (F3V_Install.configuration base) base.boundaries s H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (accepted : (eval H (F3T_Installed.source (F3V_Install.configuration base) hashv (input (F3V_Install.configuration base) s))).2=true)
    (first : AspisR1CurrentCaller.verifier.candidate.tx1
      (GExp_FirstCode.installed (GExp_FirstPair.base (F3V_Install.configuration base).currentBase
        (F3V_Install.configuration base).reserved (F3V_Install.configuration base).query (F3V_Install.configuration base).geometry)
        (F3V_Install.configuration base).boundaries (F3V_Install.configuration base).std)
      (D1 (F3V_Install.configuration base) H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
      e.pub e.proof 10#usize () none=ok (.Ok e.saved))
    (prior : Program Bytes State Unit) (decoder : LiteralByteProtocol.Decoder)
    (owner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current (F3V_Install.configuration base).currentBase)
        (F3V_Install.configuration base).reserved (F3V_Install.configuration base).query
        (F3V_Install.configuration base).geometry (F3V_Install.configuration base).boundaries (F3V_Install.configuration base).std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives (F3V_Install.configuration base).query)
    (canonical : Port5Q1_GeometryCanonical.SessionAPrimitives (F3V_Install.configuration base).geometry)
    (domain : Port5Q1_Domain.SessionADomain (F3V_Install.configuration base).geometry)
    (multiply : (F3V_Install.configuration base).geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : (F3V_Install.configuration base).geometry.op7=ok (1#u32))
    (inverse : (F3V_Install.configuration base).geometry.op11=Port4C_InverseExecution.inverse_owned) :
    let c := F3V_Install.configuration base
    ∃ (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
      (data : RecordedBinaryExperimentBin.SourceInputs) (t : Cons_Native.Witness),
      let tr := LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2
      i.physical.bytes=bytesOf e.pub.val ∧ i.stored=bytesOf e.proof.val ∧
      OraclePortStoredParserC4.parseReached i.stored tr=some p ∧ OraclePortSelectedDraft.queries tr=some q ∧
      OraclePortStoredDecisionDraftC4.input p q tr=some data ∧
      Cons_Native.Calls (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.finish c.reserved c.query c.geometry
        (D2 c H) () e.pub e.proof e.saved.deref t ∧
      (AuS1_Finish.Collision H (F3V_Checkpoint.trace c base.boundaries s H e prior) p q ∨
        ((eval H (F3T_Installed.source c hashv (input c s))).1=(eval H (F3_Model.verifier decoder i)).1 ∧
          F3S_AcceptanceValues.Values c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2}
            H (F3V_Checkpoint.trace c base.boundaries s H e prior) p q tr data decoder i)) := by
  dsimp only
  let c := F3V_Install.configuration base
  obtain ⟨i,p,q,data,out,v,physical,stored,parser,queries,found,prepare,output,opening,prepared,guard,result⟩ :=
    PFin_WorldJoin.log base s H e hashv accepted first prior decoder owner ports canonical domain multiply one inverse
  have reached := parser
  rw [stored] at reached
  have parsed := (OraclePortStoredParserC4.parsed _ _ _ reached).1
  obtain ⟨t,calls,aux,outcome⟩ := F3V_Finish.reached c base.boundaries s H e prior p parsed ports canonical domain multiply one inverse
  refine ⟨i,p,q,data,t,physical,stored,parser,queries,found,calls,?_⟩
  rcases result with bad | ⟨logs,saved⟩
  · exact Or.inl bad
  · right
    refine ⟨logs,?_⟩
    have savedSource := saved
    rw [stored,physical] at savedSource
    have s2 := F3V_ReadModel.variant c base.boundaries s H e t calls p data v q savedSource
    have ⟨_,_,_,_,_,_,_,_,_,finishCall,_⟩ := calls
    have outcome' : F3R_Finish.Outcome c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2}
        e.proof e.saved H i.stored i.physical.bytes e.run.p p (F3V_Checkpoint.trace c base.boundaries s H e prior) := by
      rw [stored,physical];exact outcome
    exact F3S_ModelAcceptance.accepted c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2}
      e.proof e.saved H i.stored i.physical.bytes e.run.p p (F3V_Checkpoint.trace c base.boundaries s H e prior)
      s2 finishCall outcome' decoder i q _ data v rfl (OraclePortCompactDraft.parse_header _ _ parsed).2
      guard parser queries found opening
      (F3V_FirstBatchModel.accepted c base.boundaries s H e p parsed data.data _ q prepare)
      (F3V_SecondBatchModel.accepted c base.boundaries s H e p parsed data.data _ q prepare) prepare saved

#print axioms values
end AspisR1.PFin_WorldAcceptance
end
