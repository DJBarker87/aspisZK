import R1Z.ProverCommitOwnedRebase
import R1Z.ProverCommitOwnedBudget
set_option autoImplicit false
namespace R1Z.ProverCommitOwnedDecoder
open Aeneas Aeneas.Std Result AspisR1ProverStep8
open R0Z.FsStatement
open R1Z.ProverCommitStepLoop (State)
open R1Z.ProverCommitFourSteps (collect)

def localizedCaller {n : Nat} (answers : Fin n → OracleAnswer)
    (domain : Slice U8) (state : State) :=
  prover_commit_reference.limb_caller (windowHash answers (position state/8)) domain state

/-- Every scalar is checked in its own bounded window, all obtained from the
same retained global oracle. Induction transports the complete collection,
including partial error states, without a whole-array nine-block backend. -/
theorem collect_rebase {n : Nat} (answers : Fin n → OracleAnswer)
    (domain : Slice U8) (capacity : n < 2^64) (count : Nat)
    (state : State) (before : valid n state) (room : position state+16*count ≤ n*8) :
    collect (prover_commit_reference.limb_caller (blockHash answers) domain) count state =
      collect (localizedCaller answers domain) count state := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    obtain ⟨sample, current, step, invariant, lo, hi⟩ :=
      scalar_total answers domain capacity 16 state before (by omega)
    have global : prover_commit_reference.limb_caller (blockHash answers) domain state = ok (sample,current) := by
      rw [R1Z.ProverCommitStepLoop.caller_sixteen]
      exact step
    have localrun : localizedCaller answers domain state = ok (sample,current) := by
      unfold localizedCaller
      rw [← scalar_rebase answers domain capacity state before (by omega), global]
    simp only [collect, global, localrun, bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
    cases sample with
    | Err e => rfl
    | Ok value => rw [ih current invariant (by omega)]

#print axioms collect_rebase
end R1Z.ProverCommitOwnedDecoder
