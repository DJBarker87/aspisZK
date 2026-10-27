import F3T_Prefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Causal
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open F3T_Experiment F3T_Charged F3T_Prefix
/-- Every submitted transcript chain starts in the sampler charged, whether
or not the prover already read that address. In particular no accepted
transcript start can be first-read only in the terminal suffix. -/
theorem transcript_start_read (D : LiteralByteProtocol.Decoder) (P : Prover)
    (H : Bytes → State) (n : Nat) (hn : n < 33) (a : Bytes)
    (ha : firstCell ((LiteralByteProtocol.protocol D).chain H
      (eval H (projected D P)).2.1.1 (eval H (projected D P)).2.1.2 n) = some a) :
    Read (eval H (charged D P)).1 a := by
  rw [same_transcript,charged_eval] at ha
  dsimp only at ha
  rw [RawCutTranscriptRun.chain_eq] at ha
  have he : RawCutWordsFromView.frame D H (eval H (base D P)).2.1.1
      (eval H (base D P)).2.1.2 n = a := by
    unfold RawCutWordsFromView.frame
    rw [ha]
    rfl
  rw [charged_eval,← he]
  exact RawCutWordsFromView.frame_read D (fun _ _ => true) (F3T_Projection.project P) H n hn

/-- The requested dichotomy as actual address membership: a submitted
transcript start occurs in the prover log or the verifier's followed log. -/
theorem transcript_start_prover_or_followed (D : LiteralByteProtocol.Decoder) (P : Prover)
    (H : Bytes → State) (n : Nat) (hn : n < 33) (a : Bytes)
    (ha : firstCell ((LiteralByteProtocol.protocol D).chain H
      (eval H (projected D P)).2.1.1 (eval H (projected D P)).2.1.2 n) = some a) :
    Read (eval H P).1 a ∨ Read
      (eval H (RawCutProverCompiler.verifier D (fun _ _ => true)
        (eval H (F3T_Projection.project P)).2.1 (eval H (F3T_Projection.project P)).2.2)).1 a := by
  have hr := transcript_start_read D P H n hn a ha
  rw [charged_eval] at hr
  unfold base at hr
  rw [RawCutProverCompiler.experiment_eval] at hr
  change a ∈ (_ ++ _ : List (Bytes × State)).map Prod.fst at hr
  rw [List.map_append,List.mem_append] at hr
  rcases hr with hp | hv
  · apply Or.inl
    change a ∈ (eval H P).1.map Prod.fst
    simpa only [F3T_Projection.project_eval] using hp
  · apply Or.inr
    exact hv

/-- The observable reads only the charged charged, reconstructed from the
full record. Its fallback oracle values are never used. -/
def recovered (D : LiteralByteProtocol.Decoder) (P : Prover)
    (run : RawCutProverCompiler.RunView) : RawCutProverCompiler.RunView :=
  eval (OracleProgramReplay.oracleOf run.1) (charged D P)

theorem recovered_eval (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    recovered D P (eval H (projected D P)) = eval H (charged D P) := by
  apply OracleProgramReplay.eval_oracleOf H _ _ (FS.eval_consistent H _)
  obtain ⟨tail,he⟩ := chronological_prefix D P H
  intro a ha
  rw [he,List.map_append]
  exact List.mem_append_left _ ha

#print axioms transcript_start_read
#print axioms transcript_start_prover_or_followed
#print axioms recovered_eval
end AspisR1.F3T_Causal
end
