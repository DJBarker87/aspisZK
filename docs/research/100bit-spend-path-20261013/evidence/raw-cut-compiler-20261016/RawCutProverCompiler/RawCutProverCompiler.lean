import RawCutTranscriptRun
import OracleProgramRecording
import AdaptiveStatementFiatShamir

/-! An explicit oracle-program transformation: run and record the original
adaptive prover/verifier experiment, construct word metadata from that finite
record, and return the annotated proof. The external byte-based verifier
repeats only already-read cells. Public statement, acceptance, and the total
distinct-first-read budget are preserved exactly. The metadata constructor is
an explicit pure function of the recorded view, not an oracle-dependent
parameter. Its concrete commitment-cut correctness is a separate premise. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawCutProverCompiler

open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open CanonicalCutEnrichedTranscript RawCutTranscriptRun

abbrev Public := LiteralTranscript.Public
abbrev Proof := LiteralProtocol.Proof
abbrev Prover := Program Bytes State (Public × Proof)
abbrev RunView := View Bytes State ((Public × Proof) × Bool)

def verifier (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) : Public → Proof → Program Bytes State Bool :=
  FS2.verifier (LiteralByteProtocol.protocol decoder) (decisionOnBytes d)

def experiment (P : Prover) (V : Public → Proof → Program Bytes State Bool) :=
  AdaptiveStatementFiatShamir.experiment P V

theorem experiment_eval (P : Prover) (V : Public → Proof → Program Bytes State Bool)
    (H : Bytes → State) :
    eval H (experiment P V) =
      ((eval H P).1 ++ (eval H (V (eval H P).2.1 (eval H P).2.2)).1,
        ((eval H P).2, (eval H (V (eval H P).2.1 (eval H P).2.2)).2)) :=
  FS2.experiment_eval P (fun (_ : Unit) xp => V xp.1 xp.2) () H

def compiled (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool)
    (buildWords : RunView → Words) (P : Prover) : Prover :=
  bind (OracleProgramRecording.record (experiment P (verifier decoder d))) fun v =>
    Program.done (v.2.1.1, RawCutTranscriptRun.proof (buildWords v) v.2.1.2)

theorem eval_compiled (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool)
    (buildWords : RunView → Words) (P : Prover) (H : Bytes → State) :
    eval H (compiled decoder d buildWords P) =
      let v := eval H (experiment P (verifier decoder d))
      (v.1, (v.2.1.1, RawCutTranscriptRun.proof (buildWords v) v.2.1.2)) := by
  rw [compiled, eval_bind, OracleProgramRecording.eval_record]
  simp [eval]

theorem compiled_experiment_eval (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool)
    (buildWords : RunView → Words) (P : Prover) (H : Bytes → State) :
    eval H (experiment (compiled decoder d buildWords P) (verifier decoder d)) =
      let v := eval H (experiment P (verifier decoder d))
      (v.1 ++ (eval H (verifier decoder d v.2.1.1 v.2.1.2)).1,
        ((v.2.1.1, RawCutTranscriptRun.proof (buildWords v) v.2.1.2), v.2.2)) := by
  rw [experiment_eval, eval_compiled]
  dsimp only
  have he (pub : Public) (pf : Proof) (w : Words) :
      verifier decoder d pub (RawCutTranscriptRun.proof w pf) =
        verifier decoder d pub pf := RawCutTranscriptRun.verifier_eq decoder d w pub pf
  rw [he]
  have hb : (eval H (verifier decoder d
      (eval H (experiment P (verifier decoder d))).2.1.1
      (eval H (experiment P (verifier decoder d))).2.1.2)).2 =
      (eval H (experiment P (verifier decoder d))).2.2 := by
    rw [experiment_eval]
  rw [hb]

theorem public_and_acceptance (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool)
    (buildWords : RunView → Words) (P : Prover) (H : Bytes → State) :
    let original := eval H (experiment P (verifier decoder d))
    let annotated := eval H (experiment (compiled decoder d buildWords P) (verifier decoder d))
    annotated.2.1.1 = original.2.1.1 ∧ annotated.2.2 = original.2.2 := by
  dsimp only
  rw [compiled_experiment_eval]
  exact ⟨rfl, rfl⟩

/-- The internal verifier run adds no distinct calls to the complete
experiment: the external verifier repeats the same already-known cells. -/
theorem firstReads_eq (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool)
    (buildWords : RunView → Words) (P : Prover) (H : Bytes → State) :
    firstReads emptyTable
        (eval H (experiment (compiled decoder d buildWords P) (verifier decoder d))).1 =
      firstReads emptyTable (eval H (experiment P (verifier decoder d))).1 := by
  rw [compiled_experiment_eval]
  rw [experiment_eval]
  exact OracleProgramRecording.firstReads_repeat_suffix _ _

/-- A commitment already read in the original experiment has exactly the
same chronological pre-read log in the transformed experiment. -/
theorem commitment_cut_eq (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool)
    (buildWords : RunView → Words) (P : Prover) (H : Bytes → State) (frame : Bytes)
    (hframe : FS2.Duplex.Read (eval H (experiment P (verifier decoder d))).1 frame) :
    RawByteCutRecovery.cut
        (eval H (experiment (compiled decoder d buildWords P) (verifier decoder d))).1 frame =
      RawByteCutRecovery.cut (eval H (experiment P (verifier decoder d))).1 frame := by
  rw [compiled_experiment_eval]
  exact OracleProgramRecording.cut_append_of_read frame _ _ hframe

#print axioms eval_compiled
#print axioms compiled_experiment_eval
#print axioms public_and_acceptance
#print axioms firstReads_eq
#print axioms commitment_cut_eq
end AspisR1.RawCutProverCompiler
end
