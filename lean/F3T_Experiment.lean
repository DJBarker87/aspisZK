import F3_Counts
import OraclePortStoredExperimentC4
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Experiment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open CanonicalCutEnrichedTranscript (Words)
abbrev Prover := Program Bytes State F3_Model.Input
abbrev RunView := View Bytes State (F3_Model.Input × Bool)

def view (v : RunView) : RawCutProverCompiler.RunView :=
  (v.1,((v.2.1.semantic.value,v.2.1.proof),v.2.2))

def original (D : LiteralByteProtocol.Decoder) (P : Prover) : Program Bytes State (F3_Model.Input × Bool) :=
  bind P fun i => bind (F3_Model.verifier D i) fun ok => .done (i,ok)

def enrich (w : Words) (i : F3_Model.Input) : F3_Model.Input :=
  {i with proof := RawCutTranscriptRun.proof w i.proof}

def compiled (D : LiteralByteProtocol.Decoder)
    (build : RawCutProverCompiler.RunView → Words) (P : Prover) : Prover :=
  bind (OracleProgramRecording.record (original D P)) fun v => .done (enrich (build (view v)) v.2.1)

def recorded (D : LiteralByteProtocol.Decoder)
    (build : RawCutProverCompiler.RunView → Words) (P : Prover) := original D (compiled D build P)

theorem original_eval (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    eval H (original D P)=
    ((eval H P).1 ++ (eval H (F3_Model.verifier D (eval H P).2)).1,
      ((eval H P).2,(eval H (F3_Model.verifier D (eval H P).2)).2)) := by
  simp only [original,eval_bind,eval,List.append_nil]

theorem verifier_enrich (D : LiteralByteProtocol.Decoder) (w : Words) (i : F3_Model.Input) :
    F3_Model.verifier D (enrich w i)=F3_Model.verifier D i :=
  OraclePortStoredExperimentC4.verifier_enrich D (F3_Model.decision i.physical) w
    ⟨i.semantic.value,i.proof,i.stored⟩

theorem compiled_eval (D : LiteralByteProtocol.Decoder)
    (build : RawCutProverCompiler.RunView → Words) (P : Prover) (H : Bytes → State) :
    eval H (compiled D build P)=
      let v := eval H (original D P)
      (v.1,enrich (build (view v)) v.2.1) := by
  simp only [compiled,eval_bind,OracleProgramRecording.eval_record,eval,List.append_nil]

theorem recorded_eval (D : LiteralByteProtocol.Decoder)
    (build : RawCutProverCompiler.RunView → Words) (P : Prover) (H : Bytes → State) :
    eval H (recorded D build P)=
      let v := eval H (original D P)
      (v.1 ++ (eval H (F3_Model.verifier D v.2.1)).1,
        (enrich (build (view v)) v.2.1,v.2.2)) := by
  rw [recorded,original_eval,compiled_eval]
  dsimp only
  rw [verifier_enrich]
  have same : (eval H (F3_Model.verifier D (eval H (original D P)).2.1)).2=
      (eval H (original D P)).2.2 := by rw [original_eval]
  rw [same]

#print axioms original_eval
#print axioms verifier_enrich
#print axioms compiled_eval
#print axioms recorded_eval
end AspisR1.F3T_Experiment
end
