import R1Z.ProverRwEntropySequence64
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwEntropySequenceBound64
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRwEffectSource ProverRwEffectTape ProverRwEffectPrefix ProverRwEntropySequence64
variable [ExternalTypes]
attribute [local instance] Classical.propDecidable

theorem increment (limit retry : Usize) (below : retry < limit) :
    (Usize.wrapping_add retry 1#usize).val = retry.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  change (retry.val+1) % UScalar.size .Usize = retry.val+1
  apply Nat.mod_eq_of_lt
  have order : retry.val < limit.val := below
  have sized := limit.hSize
  omega

theorem reads_bound (ops : ExternalFuns) (nonce : Array U8 32#usize) (limit : Usize)
    (fuel : Nat) (retry : Usize) (events : List Event)
    (reads : List (Slice U8 × Result Reply)) :
    (model ops nonce limit fuel retry events reads).world.reads.length ≤
      reads.length + (limit.val-retry.val) := by
  induction fuel generalizing retry events reads with
  | zero => simp only [model,world]; omega
  | succ fuel ih =>
    by_cases below : retry < limit
    · have order : retry.val < limit.val := below
      simp only [model,below,if_true]
      cases events with
      | nil => simp only [world]; omega
      | cons event rest =>
        cases event with
        | full bytes =>
          by_cases bad : ProverCommitPublicNonce40.decode (ProverRwEntropyDecode64.raw bytes) = none
          · simp only [boundary,bad,if_true]
            have tail := ih (Usize.wrapping_add retry 1#usize) rest
              (reads ++ [(ProverRwEntropyObstruction.zeroInput,reply (.full bytes))])
            simp only [List.length_append,List.length_cons,List.length_nil] at tail
            rw [increment limit retry below] at tail
            omega
          · simp only [boundary,bad,if_false,world,List.length_append,List.length_cons,List.length_nil]
            omega
        | os error bytes =>
          simp only [boundary,world,List.length_append,List.length_cons,List.length_nil]
          omega
        | failed error =>
          simp only [boundary,world,List.length_append,List.length_cons,List.length_nil]
          omega
        | diverged =>
          simp only [boundary,world,List.length_append,List.length_cons,List.length_nil]
          omega
    · simp only [model,below,if_false,world]
      omega

#print axioms increment
#print axioms reads_bound
end R1Z.ProverRwEntropySequenceBound64
