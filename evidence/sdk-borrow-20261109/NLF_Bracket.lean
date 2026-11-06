import NLF_ReleaseInvariant
set_option autoImplicit false
namespace NLF_Bracket
open NLF_RefCell NLF_SdkModel

def snapshot (s : State) (a t : Nat) : State × Except ProgramError Payload :=
  match try_borrow_data s a t with
  | (s', .error e) => (s', .error e)
  | (s', .ok g) =>
    match release s' g with
    | .ok s'' => (s'', .ok (deref s' g))
    | .error _ => (s', .error .accountBorrowFailed)

theorem snapshot_ok (s : State) (a t : Nat)
    (free : (s.cells (s.accounts a).data).writer = none)
    (fresh : t ∉ (s.cells (s.accounts a).data).readers)
    (bound : (s.cells (s.accounts a).data).readers.length < 9223372036854775807) :
    snapshot s a t = (s,.ok (s.cells (s.accounts a).data).payload) := by
  unfold snapshot try_borrow_data
  rw [shared_result s _ t free fresh bound]
  simp only [shared_release s _ t free,shared_deref]

theorem snapshot_error (s : State) (a t : Nat)
    (bad : ¬ ((s.cells (s.accounts a).data).writer = none ∧
      (s.cells (s.accounts a).data).readers.length < 9223372036854775807 ∧
      t ∉ (s.cells (s.accounts a).data).readers)) :
    snapshot s a t = (s,.error .accountBorrowFailed) := by
  simp [snapshot,try_borrow_data,wrap,shared,bad]

theorem snapshot_frame (s : State) (a t : Nat) : (snapshot s a t).1 = s := by
  by_cases ok : (s.cells (s.accounts a).data).writer = none ∧
      (s.cells (s.accounts a).data).readers.length < 9223372036854775807 ∧
      t ∉ (s.cells (s.accounts a).data).readers
  · rw [snapshot_ok s a t ok.1 ok.2.2 ok.2.1]
  · rw [snapshot_error s a t ok]

#print axioms snapshot_ok
#print axioms snapshot_error
#print axioms snapshot_frame
end NLF_Bracket
