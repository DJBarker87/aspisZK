import FIp_Canonical
import FIp_Aligned
import FIp_Remaining
import F3Y_Aligned
import F3W_SourceHead
import F3U_CanonicalNative
import F3V_Leaves
import F3V_ModelAcceptance
import F3V_AllWorldRuns
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_Witness
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem witness_or_collision {F C : Type} (base : Configuration F C)
    (seed : AspisR1Stage2.Stage2Finish.FinishOps F)
    (installed : base.finish=FIn_Install.finishOps seed)
    (positions : base.stageBase.op22=ok 7527#usize ∧ base.stageBase.op21=ok 8007#usize ∧ base.stageBase.op20=ok 10055#usize)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (s : Submission) (H : Bytes → State)
    (w : CanonicalCutEnrichedTranscript.Words) (prior : Program Bytes State Unit) :
    let c := F3V_Install.configuration base
    ∀ (owner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std))
    (decoder : LiteralByteProtocol.Decoder)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives c.query)
    (canonical : Port5Q1_GeometryCanonical.SessionAPrimitives c.geometry)
    (domain : Port5Q1_Domain.SessionADomain c.geometry)
    (multiply : c.geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : c.geometry.op7=ok (1#u32)) (inverse : c.geometry.op11=Port4C_InverseExecution.inverse_owned),
    (eval H (F3T_Installed.source c hashv (input c s))).2=true →
    ∃ e : Evidence c base.boundaries s H,
    ∃ (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
      (data : RecordedBinaryExperimentBin.SourceInputs) (t : Cons_Native.Witness),
      let tr := LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2
      i.physical.bytes=bytesOf e.pub.val ∧ i.stored=bytesOf e.proof.val ∧
      OraclePortStoredParserC4.parseReached i.stored tr=some p ∧
      OraclePortSelectedDraft.queries tr=some q ∧ OraclePortStoredDecisionDraftC4.input p q tr=some data ∧
      Cons_Native.Calls (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.finish c.reserved c.query c.geometry
        (D2 c H) () e.pub e.proof e.saved.deref t ∧
      Cons_NativeBuild.Aux c.reserved c.query c.geometry (D2 c H) () e.pub e.proof e.saved.deref t ∧
      SAG_NativeFull.Shape (Tx2N_Execution.control
        (Tx2I_Install.stage (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.finish)
        c.reserved c.query c.geometry) e.proof t ∧
      FGl_PreparedAt.At c base.boundaries s H e i p q data ∧
      (AuS1_Finish.Collision H (F3V_Checkpoint.trace c base.boundaries s H e prior) p q ∨
        Nonempty (F3S_FinishWitness.Primitives c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2})) := by
  dsimp only
  intro owner decoder ports canonical domain multiply one inverse success
  obtain ⟨e,i,p,q,data,t,physical,stored,parser,queries,found,calls,aux,shape,atPrepared,result⟩ :=
    FIp_Canonical.accepted base seed installed positions hashv s H w prior
      owner decoder ports canonical domain multiply one inverse success
  refine ⟨e,i,p,q,data,t,physical,stored,parser,queries,found,calls,aux,shape,atPrepared,?_⟩
  rcases result with collision | ⟨x,continuation⟩
  · exact Or.inl collision
  · exact Or.inr ⟨x⟩

#print axioms witness_or_collision
end AspisR1.FIp_Witness
end
