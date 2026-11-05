import NIV_SnapshotSequence
set_option autoImplicit false
namespace AspisR1.NIV_SnapshotDomain
open Aeneas Aeneas.Std Result S2W_D189Entry
abbrev PE := AdapterRw.solana_program_error.ProgramError

/-- Exact transcription of the retained NGL_owned.snapshot_domain predicate.
It is a callee domain, not an arbitrary OwnedAccount invariant or success fact. -/
def domain (a : Owned) : Prop :=
  match a.length,a.bytes with
  | .Err .AccountBorrowFailed,.Err .AccountBorrowFailed => True
  | .Ok _,.Err .InvalidAccountData => True
  | .Ok n,.Ok bytes => n = Slice.len bytes ∧ bytes.val.length ≤ 58295
  | _,_ => False

/-- Every admitted snapshot length, including arbitrarily large malformed
original buffers, establishes the retained native helper domain. No small
payload fixture or successful decoding is a hypothesis. -/
theorem snapshot (e : Entry) (a l1 l2 : Nat)
    (left : l1 ≤ 58295) (right : l2 ≤ 58295) : domain (e.snapshot a l1 l2) := by
  by_cases admitted : (e.buffers (e.handles a).1).val.length = l1 ∨
      (e.buffers (e.handles a).1).val.length = l2
  · simp only [Entry.snapshot,admitted,ite_true,domain]
    exact ⟨True.intro,admitted.elim (fun h => h.trans_le left) (fun h => h.trans_le right)⟩
  · simp only [Entry.snapshot,admitted,ite_false,domain]

/-- The three ABI limits cover their complete natural-number index domain. -/
theorem first_limits (a : Nat) :
    (S2W_D189Wrappers.firstSizes a).1 ≤ 58295 ∧
    (S2W_D189Wrappers.firstSizes a).2 ≤ 58295 := by
  cases a with
  | zero => exact ⟨by change 58295 ≤ 58295; omega,by change 58295 ≤ 58295; omega⟩
  | succ n =>
    cases n with
    | zero => exact ⟨by change 1880 ≤ 58295; omega,by change 1880 ≤ 58295; omega⟩
    | succ n => exact ⟨by change 1768 ≤ 58295; omega,by change 1768 ≤ 58295; omega⟩

theorem first (e : Entry) (a : Nat) :
    domain (e.snapshot a (S2W_D189Wrappers.firstSizes a).1
      (S2W_D189Wrappers.firstSizes a).2) :=
  snapshot e a _ _ (first_limits a).1 (first_limits a).2

theorem second_limits (a : Nat) :
    (S2W_D189Wrappers.secondSizes a).1 ≤ 58295 ∧
    (S2W_D189Wrappers.secondSizes a).2 ≤ 58295 := by
  cases a with
  | zero => exact ⟨by change 58295 ≤ 58295; omega,by change 58295 ≤ 58295; omega⟩
  | succ a1 =>
      cases a1 with
      | zero => exact ⟨by change 384 ≤ 58295; omega,by change 384 ≤ 58295; omega⟩
      | succ a2 =>
          cases a2 with
          | zero => exact ⟨by change 192 ≤ 58295; omega,by change 192 ≤ 58295; omega⟩
          | succ a3 =>
              cases a3 with
              | zero => exact ⟨by change 768 ≤ 58295; omega,by change 768 ≤ 58295; omega⟩
              | succ a4 =>
                  cases a4 with
                  | zero => exact ⟨by change 128 ≤ 58295; omega,by change 256 ≤ 58295; omega⟩
                  | succ a5 =>
                      cases a5 with
                      | zero => exact ⟨by change 192 ≤ 58295; omega,by change 320 ≤ 58295; omega⟩
                      | succ a6 =>
                          exact ⟨by change 1768 ≤ 58295; omega,by change 1768 ≤ 58295; omega⟩

theorem second (e : Entry) (a : Nat) :
    domain (e.snapshot a (S2W_D189Wrappers.secondSizes a).1
      (S2W_D189Wrappers.secondSizes a).2) :=
  snapshot e a _ _ (second_limits a).1 (second_limits a).2

#print axioms snapshot
#print axioms first_limits
#print axioms first
#print axioms second_limits
#print axioms second
end AspisR1.NIV_SnapshotDomain
