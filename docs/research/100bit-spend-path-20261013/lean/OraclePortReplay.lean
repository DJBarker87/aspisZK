import OraclePortExperiment
import OracleProgramReplay

/-! Transcript reconstruction uses the sampler prefix, not equality of the
whole verifier trace with the legacy bounded-address trace. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortReplay
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler (Public Proof Prover RunView experiment)
open RawCutWordsFromView (frame frameFromView)
open OracleDecisionFeasibilityCore (Decision verifier)

/-- Every legacy sampler read is in the generalized verifier, even when the
terminal program branches adaptively on its own oracle answers. -/
theorem sampler_reads (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (H : Bytes → State) (pub : Public) (pf : Proof) (a : Bytes)
    (ha : Read (eval H (RawCutProverCompiler.verifier D (fun _ _ => false) pub pf)).1 a) :
    Read (eval H (verifier D dO pub pf)).1 a := by
  rw [RawCutProverCompiler.verifier, FS2.verifier_eval] at ha
  rw [OracleDecisionFeasibilityBudget.verifier_eval]
  change a ∈ ((_ : List (Bytes × State)) ++ _).map Prod.fst
  rw [List.map_append]
  exact List.mem_append.mpr (Or.inl ha)

theorem verifier_reads_in_experiment (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (P : Prover) (H : Bytes → State) (a : Bytes)
    (ha : Read (eval H (verifier D dO
      (eval H (experiment P (verifier D dO))).2.1.1
      (eval H (experiment P (verifier D dO))).2.1.2)).1 a) :
    Read (eval H (experiment P (verifier D dO))).1 a := by
  rw [RawCutProverCompiler.experiment_eval] at ha ⊢
  change a ∈ ((_ : List (Bytes × State)) ++ _).map Prod.fst
  simp only [List.map_append]
  exact List.mem_append.mpr (Or.inr ha)

theorem recorded_transcript_eq (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (P : Prover) (H : Bytes → State) (i : Nat) (hi : i ≤ 33) :
    let v := eval H (experiment P (verifier D dO))
    (LiteralByteProtocol.protocol D).transcript
      (OracleProgramReplay.oracleOf v.1) v.2.1.1 v.2.1.2 i =
    (LiteralByteProtocol.protocol D).transcript H v.2.1.1 v.2.1.2 i := by
  dsimp only
  apply OracleProgramReplay.transcript_eq_of_agrees
    (LiteralByteProtocol.protocol D) (RawCutTranscriptRun.decisionOnBytes (fun _ _ => false)) H
  · intro a ha
    apply OracleProgramReplay.oracleOf_eq H _ (FS.eval_consistent H _) a
    exact verifier_reads_in_experiment D dO P H a (sampler_reads D dO H _ _ a ha)
  · exact hi

theorem frameFromView_eq (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (P : Prover) (H : Bytes → State) (i : Nat) (hi : i ≤ 33) :
    let v := eval H (experiment P (verifier D dO))
    frameFromView D v i = frame D H v.2.1.1 v.2.1.2 i := by
  dsimp only [frameFromView, frame, Protocol.chain]
  rw [recorded_transcript_eq D dO P H i hi]

theorem frame_in_sampler (D : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : Public) (pf : Proof) (i : Nat) (hi : i < 33) :
    Read (eval H (RawCutProverCompiler.verifier D (fun _ _ => false) pub pf)).1
      (frame D H pub pf i) := by
  have hf := RawCutWordsFromView.frame_read D (fun _ _ => false)
    (.done (pub,pf)) H i hi
  simpa only [RawCutProverCompiler.experiment_eval, eval, List.nil_append] using hf

theorem frame_read (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (P : Prover) (H : Bytes → State) (i : Nat) (hi : i < 33) :
    let v := eval H (experiment P (verifier D dO))
    Read v.1 (frame D H v.2.1.1 v.2.1.2 i) := by
  dsimp only
  apply verifier_reads_in_experiment D dO P H
  apply sampler_reads D dO H
  exact frame_in_sampler D H _ _ i hi

#print axioms frame_in_sampler
#print axioms sampler_reads
#print axioms verifier_reads_in_experiment
#print axioms recorded_transcript_eq
#print axioms frameFromView_eq
#print axioms frame_read
end AspisR1.OraclePortReplay
end
