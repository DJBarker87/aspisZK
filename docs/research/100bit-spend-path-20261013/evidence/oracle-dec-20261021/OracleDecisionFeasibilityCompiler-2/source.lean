import OracleDecisionFeasibilityCore

/-! Oracle decision enrichment and the compiler replay law. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionFeasibilityCompiler
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open CanonicalCutEnrichedTranscript RawCutTranscriptRun
open RawCutProverCompiler (Public Proof Prover RunView experiment experiment_eval)
open OracleDecisionFeasibilityCore (Decision onBytes)

theorem verifierFrom_eq (decoder : AspisR1.LiteralByteProtocol.Decoder)
    (d : Decision) (w : Words)
    (pf : AspisR1.LiteralProtocol.Proof) (n : Nat) (P : LiteralTranscript.Prefix) :
    OracleDecisionFeasibilityCore.verifierFrom decoder d
      (proof w pf) n (enrichPrefix w P) =
    OracleDecisionFeasibilityCore.verifierFrom decoder d
      pf n P := by
  induction n generalizing P with
  | zero =>
      change onBytes d (enrichPrefix w P) (enrichMessage w (pf 33)) = onBytes d P (pf 33)
      simp only [onBytes, erasePrefix_enrich, erase_enrichMessage]
  | succ n ih =>
      change bind (LiteralByteSampler.samp (33 - (n+1)) (enrichPrefix w P)
          (enrichMessage w (pf (33 - (n+1))))).toProgram
          (fun c => OracleDecisionFeasibilityCore.verifierFrom decoder d (proof w pf) n
            ((enrichPrefix w P).ext (enrichMessage w (pf (33 - (n+1)))) c)) =
        bind (LiteralByteSampler.samp (33 - (n+1)) P (pf (33 - (n+1)))).toProgram
          (fun c => OracleDecisionFeasibilityCore.verifierFrom decoder d pf n (P.ext (pf (33 - (n+1))) c))
      rw [byte_sampler_eq]
      congr 1
      funext c
      rw [← prefix_ext]
      exact ih _

/-- Exact program equality: changing only the recovered word metadata adds
no oracle calls and preserves the byte-based verifier's acceptance. -/
theorem verifier_eq (decoder : AspisR1.LiteralByteProtocol.Decoder)
    (d : Decision) (w : Words)
    (pub : LiteralTranscript.Public) (pf : AspisR1.LiteralProtocol.Proof) :
    OracleDecisionFeasibilityCore.verifier decoder d pub (proof w pf) =
      OracleDecisionFeasibilityCore.verifier decoder d pub pf := by
  exact verifierFrom_eq decoder d w pf 33 (FS.emptyPrefix pub)

def compiled (decoder : LiteralByteProtocol.Decoder)
    (d : Decision)
    (buildWords : RunView → Words) (P : Prover) : Prover :=
  bind (OracleProgramRecording.record (experiment P (OracleDecisionFeasibilityCore.verifier decoder d))) fun v =>
    Program.done (v.2.1.1, RawCutTranscriptRun.proof (buildWords v) v.2.1.2)

theorem eval_compiled (decoder : LiteralByteProtocol.Decoder)
    (d : Decision)
    (buildWords : RunView → Words) (P : Prover) (H : Bytes → State) :
    eval H (compiled decoder d buildWords P) =
      let v := eval H (experiment P (OracleDecisionFeasibilityCore.verifier decoder d))
      (v.1, (v.2.1.1, RawCutTranscriptRun.proof (buildWords v) v.2.1.2)) := by
  rw [compiled, eval_bind, OracleProgramRecording.eval_record]
  simp [eval]

theorem compiled_experiment_eval (decoder : LiteralByteProtocol.Decoder)
    (d : Decision)
    (buildWords : RunView → Words) (P : Prover) (H : Bytes → State) :
    eval H (experiment (compiled decoder d buildWords P) (OracleDecisionFeasibilityCore.verifier decoder d)) =
      let v := eval H (experiment P (OracleDecisionFeasibilityCore.verifier decoder d))
      (v.1 ++ (eval H (OracleDecisionFeasibilityCore.verifier decoder d v.2.1.1 v.2.1.2)).1,
        ((v.2.1.1, RawCutTranscriptRun.proof (buildWords v) v.2.1.2), v.2.2)) := by
  rw [experiment_eval, eval_compiled]
  dsimp only
  have he (pub : Public) (pf : Proof) (w : Words) :
      OracleDecisionFeasibilityCore.verifier decoder d pub (RawCutTranscriptRun.proof w pf) =
        OracleDecisionFeasibilityCore.verifier decoder d pub pf := verifier_eq decoder d w pub pf
  rw [he]
  have hb : (eval H (OracleDecisionFeasibilityCore.verifier decoder d
      (eval H (experiment P (OracleDecisionFeasibilityCore.verifier decoder d))).2.1.1
      (eval H (experiment P (OracleDecisionFeasibilityCore.verifier decoder d))).2.1.2)).2 =
      (eval H (experiment P (OracleDecisionFeasibilityCore.verifier decoder d))).2.2 := by
    rw [experiment_eval]
  rw [hb]

theorem public_and_acceptance (decoder : LiteralByteProtocol.Decoder)
    (d : Decision)
    (buildWords : RunView → Words) (P : Prover) (H : Bytes → State) :
    let original := eval H (experiment P (OracleDecisionFeasibilityCore.verifier decoder d))
    let annotated := eval H (experiment (compiled decoder d buildWords P) (OracleDecisionFeasibilityCore.verifier decoder d))
    annotated.2.1.1 = original.2.1.1 ∧ annotated.2.2 = original.2.2 := by
  dsimp only
  rw [compiled_experiment_eval]
  exact ⟨rfl, rfl⟩

/-- The internal verifier run adds no distinct calls to the complete
experiment: the external verifier repeats the same already-known cells. -/
theorem firstReads_eq (decoder : LiteralByteProtocol.Decoder)
    (d : Decision)
    (buildWords : RunView → Words) (P : Prover) (H : Bytes → State) :
    firstReads emptyTable
        (eval H (experiment (compiled decoder d buildWords P) (OracleDecisionFeasibilityCore.verifier decoder d))).1 =
      firstReads emptyTable (eval H (experiment P (OracleDecisionFeasibilityCore.verifier decoder d))).1 := by
  rw [compiled_experiment_eval]
  rw [experiment_eval]
  exact OracleProgramRecording.firstReads_repeat_suffix _ _

/-- A commitment already read in the original experiment has exactly the
same chronological pre-read log in the transformed experiment. -/
theorem commitment_cut_eq (decoder : LiteralByteProtocol.Decoder)
    (d : Decision)
    (buildWords : RunView → Words) (P : Prover) (H : Bytes → State) (frame : Bytes)
    (hframe : FS2.Duplex.Read (eval H (experiment P (OracleDecisionFeasibilityCore.verifier decoder d))).1 frame) :
    RawByteCutRecovery.cut
        (eval H (experiment (compiled decoder d buildWords P) (OracleDecisionFeasibilityCore.verifier decoder d))).1 frame =
      RawByteCutRecovery.cut (eval H (experiment P (OracleDecisionFeasibilityCore.verifier decoder d))).1 frame := by
  rw [compiled_experiment_eval]
  exact OracleProgramRecording.cut_append_of_read frame _ _ hframe

#print axioms verifierFrom_eq
#print axioms verifier_eq
#print axioms eval_compiled
#print axioms compiled_experiment_eval
#print axioms public_and_acceptance
#print axioms firstReads_eq
#print axioms commitment_cut_eq
end AspisR1.OracleDecisionFeasibilityCompiler
end
