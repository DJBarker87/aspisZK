import F3T_Experiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Bounds
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open F3T_Experiment
open CanonicalCutEnrichedTranscript (Words)

theorem carriers (D : LiteralByteProtocol.Decoder)
    (build : RawCutProverCompiler.RunView → Words) (P : Prover) (H : Bytes → State) :
    let before := eval H (original D P)
    let after := eval H (recorded D build P)
    after.2.1.physical=before.2.1.physical ∧ after.2.1.semantic=before.2.1.semantic ∧
      after.2.1.stored=before.2.1.stored ∧ after.2.2=before.2.2 := by
  dsimp only
  rw [recorded_eval]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem first_reads (D : LiteralByteProtocol.Decoder)
    (build : RawCutProverCompiler.RunView → Words) (P : Prover) (H : Bytes → State) :
    firstReads emptyTable (eval H (recorded D build P)).1=
      firstReads emptyTable (eval H (original D P)).1 := by
  rw [recorded_eval,original_eval]
  exact OracleProgramRecording.firstReads_repeat_suffix _ _

/-- All-input annotated budget: preserving the physical carrier introduces no
new issued read, and repeating the same-H pass introduces no new first read. -/
theorem distinct_bound (D : LiteralByteProtocol.Decoder)
    (build : RawCutProverCompiler.RunView → Words) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length≤Q) (H : Bytes → State) :
    firstReads emptyTable (eval H (recorded D build P)).1≤Q+1161 := by
  rw [first_reads,original_eval]
  have reads := VerifierCallBudget.firstReads_le_length emptyTable
    ((eval H P).1 ++ (eval H (F3_Model.verifier D (eval H P).2)).1)
  rw [List.length_append] at reads
  exact reads.trans (Nat.add_le_add (hq H) (F3_Counts.verifier_bound D H _))

theorem log_length (D : LiteralByteProtocol.Decoder)
    (build : RawCutProverCompiler.RunView → Words) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length≤Q) (H : Bytes → State) :
    (eval H (recorded D build P)).1.length≤Q+2322 := by
  rw [recorded_eval,List.length_append,original_eval]
  simp only [List.length_append]
  have before := F3_Counts.verifier_bound D H (eval H P).2
  have after := F3_Counts.verifier_bound D H (eval H (original D P)).2.1
  rw [original_eval] at after
  dsimp only at after
  have prover := hq H
  omega

#print axioms carriers
#print axioms first_reads
#print axioms distinct_bound
#print axioms log_length
end AspisR1.F3T_Bounds
end
