import IDa_Deployed
import FJt_RunEndpoint
import FJt_DecodedPublic
import FJt_CurrentCode
import F3V_IdealBackend
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJt_GlobalTerminal
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

abbrev configuration {C : Type} (m : IDa_Deployed.Uninstalled C) (err : C) (r : NP6_StdModel.Reservation) :=
  FIp_Install.configuration err (IDa_Deployed.deployedConfiguration m err r) r

theorem value {C : Type} (m : IDa_Deployed.Uninstalled C) (err : C) (r : NP6_StdModel.Reservation)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence (configuration m err r) B s H)
    (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs)
    (atPrepared : FGl_PreparedAt.At (configuration m err r) B s H e i p q data) :
    FIr_Remaining2.Endpoint data.decoded (OraclePortStoredDecisionDraftC4.typedRows p q
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)) data.data := by
  let c:=configuration m err r
  have parser:=atPrepared.2.2.1
  rw [atPrepared.2.1] at parser
  have input:=atPrepared.2.2.2.2.1
  obtain ⟨out,v,output,opened,numeric,logs,guard⟩:=atPrepared.2.2.2.2.2.2
  obtain ⟨statement,decoded,same⟩:=FJt_DecodedPublic.value c e.pub e.semantic e.decoded
  rw [FJt_CurrentCode.same] at logs
  exact FJt_RunEndpoint.value (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry
    (IDa_Deployed.boundaries r) c.std (D1 c H)
    (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize e.saved e.run
    statement decoded same H (F3V_IdealBackend.backend H (currentDigest c)) i p q parser logs data input
#print axioms value
end AspisR1.FJt_GlobalTerminal
end
