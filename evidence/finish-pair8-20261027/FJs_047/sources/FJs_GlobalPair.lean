import FJs_GlobalFields
import FJs_OnRun
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_GlobalPair
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence
attribute [local irreducible] QuadraticAlgebra.instInv

theorem law {C : Type} (err : C) (base : Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation) :
    let c := FIp_Install.configuration err base r
    let B := (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r base)) r).boundaries
    ∀ (s : Submission) (H : Bytes → State) (e : Evidence c B s H)
      (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
      (data : RecordedBinaryExperimentBin.SourceInputs) (t : Cons_Native.Witness),
      FGl_PreparedAt.At c B s H e i p q data →
      Cons_Native.Calls (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.finish c.reserved c.query c.geometry
        (D2 c H) () e.pub e.proof e.saved.deref t →
      SAG_NativeFull.Shape (Tx2N_Execution.control
        (Tx2I_Install.stage (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.finish)
        c.reserved c.query c.geometry) e.proof t →
      FIn_Finish.PairMeaning c.finish t.v2 t.p2 data.data := by
  dsimp only
  intro s H e i p q data t atPrepared calls shape
  obtain ⟨view,am,opening,fields⟩ := FJs_GlobalFields.fields err base r s H e i p q data t atPrepared calls
  have parser := atPrepared.2.2.1
  have found := atPrepared.2.2.2.2.1
  have stored := atPrepared.2.1
  have parserProof : OraclePortStoredParserC4.parseReached (bytesOf e.proof.val)
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=some p := by
    rw [←stored];exact parser
  have read := (OraclePortStoredDecisionDraftC4.input_fields _ _ _ _ found).2
  have range : ∀ j : Fin 10,FIr_SampleRange.InBase ((view.semantic.map Prod.snd).getD (15+j.val) 0) := by
    intro j
    exact FIr_TranscriptRange.view H i.proof i.semantic.value p q view opening _
  exact FJs_OnRun.law r base.finish e.proof t _ shape rfl rfl p q _ data view parserProof read opening am fields range

#print axioms law
end AspisR1.FJs_GlobalPair
end
