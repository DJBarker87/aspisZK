import RPz7_FGl_Aligned
import RPz7_F3W_SourceHead
import RPz7_F3U_CanonicalNative
import RPz7_FGl_Leaves
import RPz7_F3V_ModelAcceptance
import RPz7_F3V_AllWorldRuns
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGl_Canonical
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem accepted {F C : Type} (base : Configuration F C)
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
      FGl_PreparedAt.At c base.boundaries s H e i p q data ∧
      (AuS1_Finish.Collision H (F3V_Checkpoint.trace c base.boundaries s H e prior) p q ∨
        ∃ x : F3S_FinishWitness.Primitives c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2},
          FGl_FinishLeaves.Holds c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2} x q p tr data →
            AuS1_Finish.Collision H (F3V_Checkpoint.trace c base.boundaries s H e prior) p q ∨
              eval H (F3T_Installed.source c hashv (input c s))=
                eval H (F3_Model.verifier decoder (input c s))) := by
  dsimp only
  intro owner decoder ports canonical domain multiply one inverse success
  let c := F3V_Install.configuration base
  obtain ⟨e,first⟩ := F3W_Runs.accepted base hashv s H decoder w success
  obtain ⟨i,p,q,data,t,physical,stored,parser,queries,found,calls,prepare,result⟩ :=
    FGl_Aligned.values base s H e hashv first prior owner decoder ports canonical domain multiply one inverse
  refine ⟨e,i,p,q,data,t,physical,stored,parser,queries,found,calls,prepare,?_⟩
  rcases result with bad | result
  · exact Or.inl bad
  · obtain ⟨logs,scalarFields,values⟩ := result
    obtain ⟨x,accepted⟩ := FGl_Leaves.actual _ _ _ _ H _ p q _ data decoder i scalarFields values
    right
    refine ⟨x,?_⟩
    intro leaves
    rcases accepted leaves with bad | modelAccepted
    · exact Or.inl bad
    · right
      obtain ⟨encoded,root,serialized,head⟩ := F3W_SourceHead.head c base.boundaries s H e hashv first
      have submission : (⟨bytesOf e.pub.val,bytesOf e.proof.val⟩ : Submission)=s := by
        cases s
        exact congrArg₂ Port1_StoredCarrier.Submission.mk e.pubBytes e.proofBytes
      have result := F3U_CanonicalNative.joined c decoder hashv H e.pub (bytesOf e.proof.val) e.semantic
        e.decoded encoded serialized i (by rw [submission];exact success) modelAccepted
        (by rw [submission];exact logs) physical stored root (by rw [submission];exact head)
      rw [submission] at result
      exact result

#print axioms accepted
end AspisR1.FGl_Canonical
end
