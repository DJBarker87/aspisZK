import AspisR1Retry34.Funs
import R1Z.ProverCommitRetry34
import R1Z.ProverCommitFields29
/-! Extracted structural retry owner, with an arbitrary effectful policy.
The eight-step bound proves all source arithmetic nonwrapping. The Kani
caller gate relates the verbatim native for-loop to this owned recursion;
source callee bodies are not assumed correct by the policy abstraction. -/
set_option autoImplicit false
namespace R1Z.ProverCommitRetrySource34
open Aeneas Aeneas.Std Result AspisR1Retry34 ProverCommitRetry34

def word (n : Nat) : Usize := ⟨BitVec.ofNat _ n⟩

theorem word_val (n : Usize) : word n.val = n := by
  apply UScalar.eq_of_val_eq
  simp only [word,UScalar.val,BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by simpa only [UScalar.size_def,UScalar.val] using n.hSize)

def decodeStep {P S : Type} : owner.Step P S ProverCommitRetry34.Error → Step P × S
  | .Done p s => (.done p,s)
  | .Retry s => (.retry,s)
  | .Stop e s => (.stop e,s)

def decodeRun {P S : Type} : owner.Run P S ProverCommitRetry34.Error → Step (Published P) × S
  | .Published p count s => (.done ⟨p,count.val⟩,s)
  | .Stopped e s => (.stop e,s)
  | .Exhausted s => (.stop .AttemptsExhausted,s)

def policy {A S P : Type} (ops : owner.Attempt A S P ProverCommitRetry34.Error) : Attempt S P :=
  fun index state => do
    let step ← ops.attempt (word index) state
    ok (decodeStep step)

theorem add_one (index : Usize) (hi : index.val ≤ 8) :
    (Usize.wrapping_add index 1#usize).val = index.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  have one : (1#usize).val=1 := by scalar_tac
  rw [one]
  apply Nat.mod_eq_of_lt
  have size : 9 < UScalar.size .Usize := by
    rw [UScalar.size_def,UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> norm_num
  omega

/-- All callbacks, successes, early errors, failure/divergence and retained
states are preserved. The policy may retain an adaptive oracle transcript. -/
theorem source_model {A S P : Type} (ops : owner.Attempt A S P ProverCommitRetry34.Error)
    (n : Nat) (fuel index : Usize) (state : S)
    (hf : fuel.val=n) (bound : fuel.val+index.val ≤ 8) :
    (do let out ← owner.retry ops fuel index state; ok (decodeRun out)) =
      run (policy ops) n index.val state := by
  induction n generalizing fuel index state with
  | zero =>
    have zero : fuel=0#usize := by scalar_tac
    rw [owner.retry]
    simp only [zero,if_true,run,bind_tc_ok]
    rfl
  | succ n ih =>
    have nonzero : fuel≠0#usize := by scalar_tac
    have sub : (Usize.wrapping_sub fuel 1#usize).val=n := by
      rw [ProverCommitFields29.sub_one fuel (by omega)]
      omega
    have add := add_one index (by omega)
    have hb : (Usize.wrapping_sub fuel 1#usize).val+
        (Usize.wrapping_add index 1#usize).val ≤ 8 := by omega
    rw [owner.retry]
    simp only [nonzero,if_false,run,policy,word_val]
    cases hs : ops.attempt index state with
    | fail e => rfl
    | div => rfl
    | ok step =>
      cases step with
      | Done p after => simp only [bind_tc_ok,decodeStep,decodeRun,lift,add]; rfl
      | Stop e after => rfl
      | Retry after =>
        simp only [bind_tc_ok,decodeStep,lift]
        have h := ih (Usize.wrapping_sub fuel 1#usize)
          (Usize.wrapping_add index 1#usize) after sub hb
        rw [add] at h
        exact h

/-- Exact fixed eight-attempt owner. This is a control theorem, not a
whole-prover refinement or an entropy/reservation distribution law. -/
theorem eight_source {A S P : Type} (ops : owner.Attempt A S P ProverCommitRetry34.Error) (state : S) :
    (do let out ← owner.retry ops 8#usize 0#usize state; ok (decodeRun out)) =
      eight (policy ops) state := by
  exact source_model ops 8 8#usize 0#usize state (by scalar_tac) (by scalar_tac)

#print axioms word_val
#print axioms add_one
#print axioms source_model
#print axioms eight_source
end R1Z.ProverCommitRetrySource34
