import PFin_WorldCanonical
import PFin_WorldAcceptance
import F3V_Leaves
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
namespace AspisR1.PFin_CanonicalJoin
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem accepted {F C : Type} (base : Configuration F C) (s : Submission) (H : Bytes → State)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (accepted : (eval H (F3T_Installed.source (F3V_Install.configuration base) hashv (input (F3V_Install.configuration base) s))).2=true)
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
    ∃ e : Evidence c base.boundaries s H,
    ∃ (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
      (data : RecordedBinaryExperimentBin.SourceInputs) (t : Cons_Native.Witness),
      let tr := LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2
      i.physical.bytes=bytesOf e.pub.val ∧ i.stored=bytesOf e.proof.val ∧
      OraclePortStoredParserC4.parseReached i.stored tr=some p ∧ OraclePortSelectedDraft.queries tr=some q ∧
      OraclePortStoredDecisionDraftC4.input p q tr=some data ∧
      Cons_Native.Calls (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.finish c.reserved c.query c.geometry
        (D2 c H) () e.pub e.proof e.saved.deref t ∧
      (AuS1_Finish.Collision H (F3V_Checkpoint.trace c base.boundaries s H e prior) p q ∨
        ∃ x : F3S_FinishWitness.Primitives c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2},
          F3T_Leaves.Holds c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2} x q p tr data →
            AuS1_Finish.Collision H (F3V_Checkpoint.trace c base.boundaries s H e prior) p q ∨
              eval H (F3T_Installed.source c hashv (input c s))=eval H (F3_Model.verifier decoder (input c s))) := by
  dsimp only
  let c := F3V_Install.configuration base
  let w := CanonicalCutEnrichedTranscript.wordsFromMaps (fun _=>none) (fun _=>none) (fun _=>none)
  obtain ⟨e,first⟩ := PFin_WorldRuns.accepted base hashv s H decoder w accepted
  obtain ⟨i,p,q,data,t,physical,stored,parser,queries,found,calls,result⟩ :=
    PFin_WorldAcceptance.values base s H e hashv accepted first prior decoder owner ports canonical domain multiply one inverse
  refine ⟨e,i,p,q,data,t,physical,stored,parser,queries,found,calls,?_⟩
  rcases result with bad | ⟨logs,values⟩
  · exact Or.inl bad
  · right
    obtain ⟨x,cont⟩ := F3V_Leaves.actual c.finish t.v2 t.p2 _ H _ p q _ data decoder i values
    refine ⟨x,?_⟩
    intro leaves
    rcases cont leaves with bad | modelAccepted
    · exact Or.inl bad
    · right
      exact PFin_WorldCanonical.joined c base.boundaries s H e hashv accepted first decoder i physical stored logs modelAccepted

#print axioms accepted
end AspisR1.PFin_CanonicalJoin
end
