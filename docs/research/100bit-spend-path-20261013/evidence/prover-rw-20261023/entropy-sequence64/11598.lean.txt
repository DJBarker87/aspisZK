import R1Z.ProverRwEntropyOwnerSequence64
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwEntropySequenceComplete64
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRwEffectSource ProverRwEffectTape ProverRwEffectPrefix ProverRwEntropySequence64
variable [ExternalTypes]
attribute [local instance] Classical.propDecidable

theorem complete (ops : ExternalFuns) (nonce : Array U8 32#usize) (limit : Usize)
    (fuel : Nat) (retry : Usize) (events : List Event)
    (reads : List (Slice U8 × Result Reply))
    (enough : limit.val-retry.val < fuel) (next : Usize) :
    (model ops nonce limit fuel retry events reads).boundary ≠ .retry next := by
  induction fuel generalizing retry events reads with
  | zero => omega
  | succ fuel ih =>
    by_cases below : retry < limit
    · have order : retry.val < limit.val := below
      simp only [model,below,if_true]
      cases events with
      | nil => simp only [Boundary.noConfusion,ne_eq,reduceCtorEq,not_false_eq_true]
      | cons event rest =>
        cases event with
        | full bytes =>
          by_cases bad : ProverCommitPublicNonce40.decode (ProverRwEntropyDecode64.raw bytes) = none
          · simp only [boundary,bad,if_true]
            apply ih
            rw [ProverRwEntropySequenceBound64.increment limit retry below]
            omega
          · simp only [boundary,bad,if_false,ne_eq,reduceCtorEq,not_false_eq_true]
        | os error bytes => simp only [boundary,ne_eq,reduceCtorEq,not_false_eq_true]
        | failed error => simp only [boundary,ne_eq,reduceCtorEq,not_false_eq_true]
        | diverged => simp only [boundary,ne_eq,reduceCtorEq,not_false_eq_true]
    · simp only [model,below,if_false,ne_eq,reduceCtorEq,not_false_eq_true]

/-- Seventeen interpreter steps cover every actual sixteen-fill source cap
path. A missing reply is still an explicit request boundary, never a made-up
OS error; no artificial interpreter retry boundary remains. -/
theorem owner_complete (ops : ExternalFuns) (nonce : Array U8 32#usize) (events : List Event)
    (reads : List (Slice U8 × Result Reply)) (next : Usize) :
    (@ProverRwEffectOwner.worldOwner _ (install ops) nonce (world events reads)).boundary ≠ .retry next := by
  rw [ProverRwEntropyOwnerSequence64.owner_exact]
  unfold ProverRwEntropyOwnerSequence64.selected
  split
  · simp only [ne_eq,reduceCtorEq,not_false_eq_true]
  · exact complete ops nonce 16#usize 17 0#usize events reads (by decide) next

#print axioms complete
#print axioms owner_complete
end R1Z.ProverRwEntropySequenceComplete64
