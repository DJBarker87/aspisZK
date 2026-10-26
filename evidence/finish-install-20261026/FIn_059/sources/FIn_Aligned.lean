import FIn_SourceFinish
import FIn_Derived
import F3Y_ReadModel
import F3Y_PreparedAt
import F3W_LogJoin
import F3V_ReadModel
import F3S_ModelAcceptance
import F3S_AcceptanceValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIn_Aligned
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem values {F C : Type} (base : Configuration F C)
    (seed : AspisR1Stage2.Stage2Finish.FinishOps F)
    (installed : base.finish=FIn_Install.finishOps seed)
    (positions : base.stageBase.op22=ok 7527#usize ∧ base.stageBase.op21=ok 8007#usize ∧ base.stageBase.op20=ok 10055#usize)
    (s : Submission) (H : Bytes → State)
    (e : Evidence (F3V_Install.configuration base) base.boundaries s H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (first : AspisR1CurrentCaller.verifier.candidate.tx1
      (GExp_FirstCode.installed (GExp_FirstPair.base base.currentBase base.reserved base.query base.geometry)
        (F3V_Install.configuration base).boundaries base.std)
      (D1 (F3V_Install.configuration base) H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
      e.pub e.proof 10#usize () none=ok (.Ok e.saved))
    (prior : Program Bytes State Unit) :
    let c := F3V_Install.configuration base
    ∀
    (owner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std))
    (decoder : LiteralByteProtocol.Decoder)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives c.query)
    (canonical : Port5Q1_GeometryCanonical.SessionAPrimitives c.geometry)
    (domain : Port5Q1_Domain.SessionADomain c.geometry)
    (multiply : c.geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : c.geometry.op7=ok (1#u32)) (inverse : c.geometry.op11=Port4C_InverseExecution.inverse_owned),
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
      F3Y_PreparedAt.At c base.boundaries s H e i p q data ∧
      (AuS1_Finish.Collision H (F3V_Checkpoint.trace c base.boundaries s H e prior) p q ∨
        (eval H (F3T_Installed.source c hashv (input c s))).1=(eval H (F3_Model.verifier decoder i)).1 ∧
        F3Y_FinishFields.Holds t.p2 data.data ∧
        (∀ x : F3S_FinishWitness.Primitives c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2},
          FIn_Derived.Holds c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2} x p q tr data.data) ∧
        F3S_AcceptanceValues.Values c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2}
          H (F3V_Checkpoint.trace c base.boundaries s H e prior) p q tr data decoder i) := by
  dsimp only
  let c := F3V_Install.configuration base
  intro owner decoder ports canonical domain multiply one inverse
  obtain ⟨i,p,q,data,out,v,physical,stored,parser,queries,found,prepare,output,opening,prepared,preparationLog,guard⟩ := e.prepared
  rw [F3R_PreparationInstall.code] at preparationLog
  have logs := F3W_LogJoin.joined base s H e hashv first prior decoder owner ports canonical domain
    multiply one inverse i p q data out v physical stored parser queries found prepare output opening
    prepared preparationLog guard
  have parserProof : OraclePortStoredParserC4.parseReached (bytesOf e.proof.val)
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=some p := by
    rw [←stored];exact parser
  have parsed := (OraclePortStoredParserC4.parsed _ _ _ parserProof).1
  obtain ⟨t,calls,aux,shape,outcome⟩ := FIn_SourceFinish.reached c base.boundaries s H e prior p parsed ports canonical domain multiply one inverse
  change AuS1_Recovery.log _ _ _ _ _ _ _ _=_ at preparationLog
  refine ⟨i,p,q,data,t,physical,stored,parser,queries,found,calls,aux,shape,⟨physical,stored,parser,queries,found,prepare,out,v,output,opening,prepared,preparationLog,guard⟩,?_⟩
  rcases logs with bad | logs
  · exact Or.inl bad
  have ten := F3V_Ten.outcome c base.boundaries s H e prior p parsed
  have saved := F3N_TenInput.same_input e.run H (F3V_Checkpoint.trace c base.boundaries s H e prior) p ten
    ports q _ data prepare parserProof found canonical domain multiply one inverse
  rcases saved with bad | good
  · exact Or.inl bad
  · right
    have savedSource := F3V_WriterModel.saved c base.boundaries s H e owner ports out output
    rw [prepared,good.1] at savedSource
    have saved := savedSource
    rw [←stored,←physical] at saved
    have scalarFields := F3Y_ReadModel.fields c base.boundaries s H e t calls p data v q savedSource
    have fields := F3N_ReaderNumeric.saved_ten (Op5T_Concrete.stage (AuS1_Install.base c.stageBase))
      c.reserved c.query (D2 c H) () e.saved.deref e.proof e.pub e.saved t.p2 t.saved2 H
      _ _ _ _ (by rfl) rfl savedSource calls.1
    have size : t.saved2.weights.val.length=64 := by
      rw [fields.1.weights]
      simp only [List.length_map,List.length_ofFn]
    have read := (OraclePortStoredDecisionDraftC4.input_fields _ _ _ _ found).2
    have derived : ∀ x : F3S_FinishWitness.Primitives c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2},
        FIn_Derived.Holds c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2} x p q _ data.data := by
      intro x
      exact FIn_Derived.derive c.finish seed installed
        (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.reserved c.query c.geometry (D2 c H) ()
        e.pub e.proof e.saved.deref t calls aux size _ shape positions.1 rfl rfl positions.2.1 positions.2.2
        p q _ data.data parserProof read x
    refine ⟨logs,scalarFields,derived,?_⟩
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
end AspisR1.FIn_Aligned
end
