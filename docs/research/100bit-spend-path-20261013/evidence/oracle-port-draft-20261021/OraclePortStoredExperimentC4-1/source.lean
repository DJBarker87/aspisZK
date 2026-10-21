import OraclePortExperiment

/-! Minimal additional stored-proof input. The 33-row protocol, message bound,
public statement and terminal message remain unchanged. Stored bytes are
chosen by the prover and preserved exactly by the annotation compiler. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortStoredExperimentC4
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open RawCutProverCompiler (Public Proof)
open CanonicalCutEnrichedTranscript (Words)

structure Input where
  public : Public
  proof : Proof
  stored : Bytes

abbrev Prover := Program Bytes State Input
abbrev Decision := Bytes → OraclePortExperiment.Decision
abbrev RunView := View Bytes State (Input × Bool)

def view (v : RunView) : RawCutProverCompiler.RunView :=
  (v.1, ((v.2.1.public,v.2.1.proof),v.2.2))

def verifier (D : LiteralByteProtocol.Decoder) (d : Decision) (i : Input) :
    Program Bytes State Bool :=
  OraclePortExperiment.verifier D (d i.stored) i.public i.proof

def original (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover) :
    Program Bytes State (Input × Bool) :=
  bind P fun i => bind (verifier D d i) fun ok => .done (i,ok)

def enrich (w : Words) (i : Input) : Input :=
  { i with proof := RawCutTranscriptRun.proof w i.proof }

def compiled (D : LiteralByteProtocol.Decoder) (d : Decision)
    (build : RawCutProverCompiler.RunView → Words) (P : Prover) : Prover :=
  bind (OracleProgramRecording.record (original D d P)) fun v =>
    .done (enrich (build (view v)) v.2.1)

def recorded (D : LiteralByteProtocol.Decoder) (d : Decision)
    (build : RawCutProverCompiler.RunView → Words) (P : Prover) :=
  original D d (compiled D d build P)

theorem original_eval (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) :
    eval H (original D d P) =
      ((eval H P).1 ++ (eval H (verifier D d (eval H P).2)).1,
        ((eval H P).2,(eval H (verifier D d (eval H P).2)).2)) := by
  simp only [original,eval_bind,eval,List.append_nil]

theorem verifier_enrich (D : LiteralByteProtocol.Decoder) (d : Decision)
    (w : Words) (i : Input) : verifier D d (enrich w i) = verifier D d i :=
  OracleDecisionFeasibilityCompiler.verifier_eq D (d i.stored) w i.public i.proof

theorem compiled_eval (D : LiteralByteProtocol.Decoder) (d : Decision)
    (build : RawCutProverCompiler.RunView → Words) (P : Prover) (H : Bytes → State) :
    eval H (compiled D d build P) =
      let v := eval H (original D d P)
      (v.1,enrich (build (view v)) v.2.1) := by
  simp only [compiled,eval_bind,OracleProgramRecording.eval_record,eval,List.append_nil]

theorem recorded_eval (D : LiteralByteProtocol.Decoder) (d : Decision)
    (build : RawCutProverCompiler.RunView → Words) (P : Prover) (H : Bytes → State) :
    eval H (recorded D d build P) =
      let v := eval H (original D d P)
      (v.1 ++ (eval H (verifier D d v.2.1)).1,
        (enrich (build (view v)) v.2.1,v.2.2)) := by
  rw [recorded,original_eval,compiled_eval]
  dsimp only
  rw [verifier_enrich]
  have same : (eval H (verifier D d (eval H (original D d P)).2.1)).2 =
      (eval H (original D d P)).2.2 := by
    rw [original_eval]
  rw [same]

theorem stored_and_public_and_acceptance (D : LiteralByteProtocol.Decoder) (d : Decision)
    (build : RawCutProverCompiler.RunView → Words) (P : Prover) (H : Bytes → State) :
    let before := eval H (original D d P)
    let after := eval H (recorded D d build P)
    after.2.1.stored = before.2.1.stored ∧
      after.2.1.public = before.2.1.public ∧ after.2.2 = before.2.2 := by
  dsimp only
  rw [recorded_eval]
  exact ⟨rfl,rfl,rfl⟩

theorem first_reads (D : LiteralByteProtocol.Decoder) (d : Decision)
    (build : RawCutProverCompiler.RunView → Words) (P : Prover) (H : Bytes → State) :
    firstReads emptyTable (eval H (recorded D d build P)).1 =
      firstReads emptyTable (eval H (original D d P)).1 := by
  rw [recorded_eval,original_eval]
  exact OracleProgramRecording.firstReads_repeat_suffix _ _

/-- All-input per-stored-proof budget: no oracle-dependent fixed decision is
smuggled into the old prover interface. -/
def Budget (d : Decision) : Prop := ∀ stored, OraclePortExperiment.Budget (d stored)

theorem verifier_budget (D : LiteralByteProtocol.Decoder) (d : Decision)
    (hb : Budget d) (H : Bytes → State) (i : Input) :
    (eval H (verifier D d i)).1.length ≤ 1161 :=
  OraclePortExperiment.verifier_budget D (d i.stored) (hb i.stored) H i.public i.proof

theorem recorded_length (D : LiteralByteProtocol.Decoder) (d : Decision)
    (build : RawCutProverCompiler.RunView → Words) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (hb : Budget d) (H : Bytes → State) :
    (eval H (recorded D d build P)).1.length ≤ Q + 2322 := by
  rw [recorded_eval, List.length_append,original_eval]
  simp only [List.length_append]
  have h1 := verifier_budget D d hb H (eval H P).2
  have h2 := verifier_budget D d hb H (eval H (original D d P)).2.1
  rw [original_eval] at h2
  dsimp only at h2
  have hp := hq H
  omega

#print axioms original_eval
#print axioms verifier_enrich
#print axioms compiled_eval
#print axioms recorded_eval
#print axioms stored_and_public_and_acceptance
#print axioms first_reads
#print axioms verifier_budget
#print axioms recorded_length
end AspisR1.OraclePortStoredExperimentC4
end
