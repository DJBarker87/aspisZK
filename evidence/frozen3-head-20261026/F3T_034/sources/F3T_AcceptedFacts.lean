import F3T_CheckedView
import OraclePortCleanModel
import F3T_Tag
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_AcceptedFacts
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_Charged F3T_Canon

 theorem accepted_facts (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State,(eval H P).1.length≤Q) (H : Bytes → State)
    (hc : ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
      (eval H (projected D (canon P))))
    (ha : (eval H (projected D (canon P))).2.2=true) :
    ∃ checks : LiteralAcceptanceTerminal.Checks (eval H (projected D (canon P))).2.1.1
        ((LiteralByteProtocol.protocol D).transcript H (eval H (projected D (canon P))).2.1.1
          (eval H (projected D (canon P))).2.1.2 33).rounds,
      RawCutTranscriptRun.proof (RawCutWordsFromRunExecutableBin.wordsFromRun
        (eval H (projected D (canon P)))) (eval H (projected D (canon P))).2.1.2=
        (eval H (projected D (canon P))).2.1.2 ∧
      (eval H (base D (canon P))).2.1.1.tag=2 := by
  let CP := canon P
  let d := F3_Model.decision (eval H CP).2.physical (eval H CP).2.stored
  let RP := F3T_Projection.project CP
  have same : eval H (projected D CP)=eval H (OraclePortExperiment.recorded D d RP) := by
    rw [projected_eval,F3T_Projection.recorded_view]
  have firstAccepted : (eval H (original D CP)).2.2=true := by
    simpa only [projected_eval,view,recorded_eval] using ha
  have checksRaw := F3T_CheckedView.checks D P Q hq H hc firstAccepted
  have checksF := checksRaw
  rw [same] at checksF
  have fixed := (OraclePortCleanModel.extractor_word_alignment D d RP H checksF).2
  have firstRaw : (eval H (OraclePortExperiment.original D d RP)).2.2=true := by
    have orig := F3T_Projection.original_view D CP H
    exact (congrArg (fun v : RawCutProverCompiler.RunView=>v.2.2) orig).symm.trans firstAccepted
  have admit : OraclePortAdmission.admit d=d :=
    F3T_Decision.admitted (eval H CP).2.physical (eval H CP).2.stored
  have tag := F3T_Tag.base_tag D d admit RP H firstRaw
  refine ⟨checksRaw,?_,tag⟩
  rw [same]
  exact fixed
#print axioms accepted_facts
end AspisR1.F3T_AcceptedFacts
end
