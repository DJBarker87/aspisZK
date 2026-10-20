import R1Z.ProverCommitExtractedStep

/-! The actual extracted I32-counter loop composes sixteen symbolic steps.
The induction does not normalize any concrete expander or oracle query. -/
set_option autoImplicit false
namespace R1Z.ProverCommitExtractedStep
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1ProverCommitReference R1Z.ProverCommitReferenceSource

theorem counter_increment (attempts : I32) (lo : 0 ≤ attempts.val)
    (hi : attempts.val < 16) :
    (I32.wrapping_add attempts 1#i32).val = attempts.val + 1 := by
  simp only [I32.wrapping_add_val_eq]
  change Int.bmod (attempts.val + 1) 4294967296 = attempts.val + 1
  rw [Int.bmod_eq_emod]
  have hm : (attempts.val + 1) % 4294967296 = attempts.val + 1 :=
    Int.emod_eq_of_lt (by omega) (by omega)
  norm_num only [Nat.cast_ofNat]
  rw [hm]
  split_ifs <;> omega

theorem reference_loop_composition (hash : Hash) (domain : Slice U8)
    (n : Nat) (state : State) (attempts : I32) (result : Sample)
    (lo : 0 ≤ attempts.val) (remaining : attempts.val + (n : Int) = 16) :
    prover_commit_reference.limb_loop hash domain state attempts result = (do
      let (after, sampled) ← iterate (step hash domain) n (state, result)
      ok (sampled, after)) := by
  induction n generalizing state attempts result with
  | zero =>
    have stop : ¬ attempts < 16#i32 := by scalar_tac
    rw [prover_commit_reference.limb_loop, loop]
    simp only [prover_commit_reference.limb_loop.body, stop, if_false,
      iterate, bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
  | succ n ih =>
    have running : attempts < 16#i32 := by scalar_tac
    have hi : attempts.val < 16 := by omega
    have inc := counter_increment attempts lo hi
    rw [prover_commit_reference.limb_loop, loop]
    dsimp only
    rw [extracted_body hash domain state attempts result running]
    simp only [iterate]
    cases hs : step hash domain (state, result) with
    | fail error => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨after, sampled⟩
      simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
      have recur :=  ih after (I32.wrapping_add attempts 1#i32) sampled
        (by omega) (by push_cast; omega)
      simpa only [prover_commit_reference.limb_loop, bind_assoc_eq] using recur

theorem reference_limb_sixteen (hash : Hash) (domain : Slice U8) (state : State) :
    prover_commit_reference.limb hash domain state = (do
      let (after, sampled) ← iterate (step hash domain) 16
        (state, .Err state_only_hiding.StateOnlyMaskBuildError.MaskSampleExhausted)
      ok (sampled, after)) := by
  exact reference_loop_composition hash domain 16 state 0#i32 _ (by decide) (by decide)

#print axioms counter_increment
#print axioms reference_loop_composition
#print axioms reference_limb_sixteen
end R1Z.ProverCommitExtractedStep
