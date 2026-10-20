import RawCutProverCompiler

/-! Feasibility only: a terminal oracle decision, with exact pure embedding. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionFeasibilityCore
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutTranscriptRun RawCutProverCompiler

abbrev Decision := ErasedPrefix → ErasedMessage → Program Bytes State Bool

def onBytes (dO : Decision) (p : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) : Program Bytes State Bool :=
  dO (LiteralTranscript.erasePrefix p) (LiteralTranscript.erase m)

def lift (d : ErasedPrefix → ErasedMessage → Bool) : Decision :=
  fun p m => .done (d p m)

def verifierFrom (D : LiteralByteProtocol.Decoder) (dO : Decision) (pf : Proof) :
    Nat → LiteralTranscript.Prefix → Program Bytes State Bool
  | 0, p => onBytes dO p (pf 33)
  | n + 1, p => bind (LiteralByteSampler.samp (33 - (n + 1)) p
      (pf (33 - (n + 1)))).toProgram fun c =>
        verifierFrom D dO pf n (p.ext (pf (33 - (n + 1))) c)

def verifier (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (pub : Public) (pf : Proof) : Program Bytes State Bool :=
  verifierFrom D dO pf 33 (emptyPrefix pub)

def original (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover) :=
  experiment P (verifier D dO)

def recorded (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover) :=
  OracleProgramRecording.record (original D dO P)

theorem lift_from (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (pf : Proof)
    (n : Nat) (p : LiteralTranscript.Prefix) :
    verifierFrom D (lift d) pf n p =
      FS2.verifierFrom (LiteralByteProtocol.protocol D) (decisionOnBytes d) pf n p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    change bind _ (fun c => verifierFrom D (lift d) pf n _) = bind _ (fun c => _)
    congr 1
    funext c
    exact ih _

theorem lift_verifier (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (pub : Public) (pf : Proof) :
    verifier D (lift d) pub pf = RawCutProverCompiler.verifier D d pub pf :=
  lift_from D d pf 33 (emptyPrefix pub)

theorem lift_experiment (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) :
    original D (lift d) P = experiment P (RawCutProverCompiler.verifier D d) := by
  unfold original
  have h : verifier D (lift d) = RawCutProverCompiler.verifier D d := by
    funext pub pf
    exact lift_verifier D d pub pf
  rw [h]

/-- Equality of the entire evaluated view entails every event/projection,
including log, public output and acceptance, without a distributional premise. -/
theorem lift_view (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) :
    eval H (original D (lift d) P) =
      eval H (experiment P (RawCutProverCompiler.verifier D d)) ∧
    eval H (recorded D (lift d) P) =
      let v := eval H (experiment P (RawCutProverCompiler.verifier D d)); (v.1, v) := by
  constructor
  · rw [lift_experiment]
  · rw [recorded, OracleProgramRecording.eval_record, lift_experiment]

/-- Universally quantified predicates of the old program transport literally. -/
theorem lift_special_case (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (property : Program Bytes State ((Public × Proof) × Bool) → Prop) :
    property (original D (lift d) P) ↔
      property (experiment P (RawCutProverCompiler.verifier D d)) := by
  rw [lift_experiment]

#print axioms lift_from
#print axioms lift_verifier
#print axioms lift_experiment
#print axioms lift_view
#print axioms lift_special_case
end AspisR1.OracleDecisionFeasibilityCore
end
