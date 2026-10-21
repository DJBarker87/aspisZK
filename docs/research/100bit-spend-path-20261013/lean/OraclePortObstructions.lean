import OraclePortAdmission
import D0ErasedWordObstruction
import OracleDecisionMultiRecovery

/-! Precise interface obstructions. Neither result is an attack on the frozen
verifier, nor a refutation of collision-conditioned selected-leaf binding. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortObstructions
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutTranscriptRun (ErasedPrefix)
open D0ErasedWordObstruction
open OracleDecisionMultiTree

/-- Even an effectful reader cannot reproduce arbitrary hidden metadata
universally: identical erased inputs run the identical program under H.
This deliberately does not quantify only over checked, clean source runs. -/
theorem no_universal_oracle_final_reader (H : Bytes → State)
    (pub : LiteralTranscript.Public) (b : LiteralTranscript.BytesMessage)
    (c : LiteralTranscript.Challenge) :
    ¬ ∃ read : ErasedPrefix → Program Bytes State (Option LiteralTranscript.VWord),
      ∀ p : LiteralTranscript.Prefix,
        (eval H (read (LiteralTranscript.erasePrefix p))).2 = LiteralTranscript.vAt p.rounds := by
  rintro ⟨read, correct⟩
  have h0 := correct (wordPrefix pub b c (fun _ => 0))
  have h1 := correct (wordPrefix pub b c (fun _ => 1))
  rw [prefix_read] at h0 h1
  rw [prefix_erased pub b c (fun _ => 0) (fun _ => 1)] at h0
  have same := Option.some.inj (h0.symm.trans h1)
  exact zero_ne_one (congrFun same 0)

def suppliedCommit (r : State) : Commitment := ⟨.supplied r, r⟩

theorem suppliedCommit_accepts (H : Bytes → State) (r : State) (n : Nat) :
    (eval H (verifyTrees (List.replicate n (suppliedCommit r)))).2 = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [List.replicate_succ, verifyTrees, suppliedCommit, execute, eval_bind, eval,
      decide_true, Bool.true_and] using ih

/-- Admissible is only a call-count condition. Its duplicate allowance can
be spent on arbitrary bytes while every tree is supplied rather than opened.
Thus accepted_roots plus Admissible cannot supply a parser/coverage theorem. -/
theorem accepted_without_opened_leaves (H : Bytes → State) (r : State) :
    ∃ (cs : List Commitment) (duplicates frames : List Bytes),
      Admissible cs duplicates frames ∧
      (eval H (terminal cs duplicates frames)).2 = true ∧ totalLeaves cs = 0 := by
  refine ⟨List.replicate 6 (suppliedCommit r), List.replicate 66 [], List.replicate 6 [], ?_, ?_, ?_⟩
  · simp [Admissible, totalSiblings, totalLeaves, suppliedCommit, siblings, leaves]
  · simpa only [terminal, eval_bind] using suppliedCommit_accepts H r 6
  · simp [totalLeaves, suppliedCommit, leaves]

#print axioms no_universal_oracle_final_reader
#print axioms suppliedCommit_accepts
#print axioms accepted_without_opened_leaves
end AspisR1.OraclePortObstructions
end
