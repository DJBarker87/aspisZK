import R1Z.ProverCommitOwnedSequence
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitOwnedDecoder
open Aeneas Aeneas.Std Result AspisR1ProverStep8
open R0Z.FsStatement R1Z.FinalR1PBin
open R1Z.ProverCommitStepLoop (State)
open R1Z.ProverCommitSequentialFibres R1Z.ProverCommitWordCarrier
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
local notation "F" => sourceBase (K := K)

theorem decode_no_values {W A : Type} [Fintype W] (d : W → Option A)
    (n r : Nat) (ws : Fin n → W) :
    (decodeWords d n 0 r ws).map (valuesList 0) = some [] := by
  cases n <;> rfl

/-- Symbolic induction over the remaining stream. The retry budget is explicit;
the proof never expands the protocol-sized collection or block carrier. -/
theorem sequence_model {blocks : Nat} (answers : Fin blocks → OracleAnswer)
    (domain : Slice U8) (capacity : blocks < 2^64) (n L r : Nat)
    (state : State) (before : valid blocks state) (cache : cacheValid answers state)
    (fits : position state+n ≤ blocks*8) (budget : r+16*L ≤ n)
    (ws : Fin n → R1Z.CommitReadsR1.Word)
    (agrees : ∀ i : Fin n,
      wordsE blocks answers ⟨position state+i.val, by have := i.isLt; omega⟩ = ws i) :
    sequence (K := K) (blockHash answers) domain (L+1) r state =
      (decodeWords (accepted (K := K)) n (L+1) r ws).map (valuesList (L+1)) := by
  induction n generalizing L r state with
  | zero =>
    have zr : r = 0 := by omega
    subst r
    rfl
  | succ n ih =>
    cases r with
    | zero => rfl
    | succ r =>
      obtain ⟨word, after, hn⟩ := next_total answers domain state before (by omega)
      have progress := next_progress answers domain state after word capacity before hn
      obtain ⟨nextcache, bound, wordeq⟩ := next_cache answers domain state after word capacity before cache hn
      have head : accepted (K := K) (ws 0) =
          if word &&& 2147483647#u32 < aspis_core.field.P then
            some (fieldValue (word &&& 2147483647#u32)) else none := by
        rw [← agrees 0]
        have eq : (⟨position state+(0 : Fin (n+1)).val, by have := (0 : Fin (n+1)).isLt; omega⟩ : Fin (blocks*8)) =
            ⟨position state, bound⟩ := by apply Fin.ext; simp
        rw [eq, ← wordeq, accepted_word]
      have fit : position after+n ≤ blocks*8 := by omega
      have tail : ∀ i : Fin n,
          wordsE blocks answers ⟨position after+i.val, by have := i.isLt; omega⟩ = ws i.succ := by
        intro i
        rw [← agrees i.succ]
        apply congrArg (wordsE blocks answers)
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      rw [sequence_step, hn, decode_list_step, head]
      simp only []
      by_cases yes : word &&& 2147483647#u32 < aspis_core.field.P
      · simp only [if_pos yes]
        cases L with
        | zero => rw [decode_no_values]; rfl
        | succ L =>
          rw [ih L 16 after progress.1 nextcache fit (by omega) (fun i => ws i.succ) tail]
      · simp only [if_neg yes]
        exact ih L r after progress.1 nextcache fit (by omega) (fun i => ws i.succ) tail

#print axioms decode_no_values
#print axioms sequence_model
end R1Z.ProverCommitOwnedDecoder
