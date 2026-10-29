import PV_DIAG3_Drop
/-! Deployed Linux futex Once::state and LazyLock::drop. The exclusive
get_mut load is caller-owned memory; no atomic load, lock or syscall occurs.
The invalid-state panic is retained, and is not assigned a silent execution. -/
set_option autoImplicit false
namespace PV_DIAG4
open PV_DIAG3
variable {S : Type}
def onceState (word : Nat) (invalid : Op S LazyState) : Op S LazyState :=
 if word = 3 then PV_DIAG3.pure .incomplete
 else if word = 2 then PV_DIAG3.pure .poisoned
 else if word = 0 then PV_DIAG3.pure .complete
 else invalid
def lazyDropWord (word : Nat) (dropClosure dropValue : Op S Unit)
 (invalid : Op S LazyState) : Op S Unit :=
 sequence (onceState word invalid) (fun state => lazyDrop state dropClosure dropValue)
theorem once_incomplete (invalid : Op S LazyState) :
 onceState 3 invalid = PV_DIAG3.pure .incomplete := by simp [onceState]
#print axioms once_incomplete
theorem once_poisoned (invalid : Op S LazyState) :
 onceState 2 invalid = PV_DIAG3.pure .poisoned := by simp [onceState]
#print axioms once_poisoned
theorem once_complete (invalid : Op S LazyState) :
 onceState 0 invalid = PV_DIAG3.pure .complete := by simp [onceState]
#print axioms once_complete
theorem once_invalid (n : Nat) (invalid : Op S LazyState)
 (h3 : n ≠ 3) (h2 : n ≠ 2) (h0 : n ≠ 0) :
 onceState n invalid = invalid := by simp [onceState,h3,h2,h0]
#print axioms once_invalid
theorem poisoned_drop_exact (f v : Op S Unit) (invalid : Op S LazyState) :
 lazyDropWord 2 f v invalid = PV_DIAG3.pure () := by
 funext s; simp [lazyDropWord,once_poisoned,sequence,pure_bind,lazyDrop]
#print axioms poisoned_drop_exact
theorem incomplete_drop_exact (f v : Op S Unit) (invalid : Op S LazyState) :
 lazyDropWord 3 f v invalid = f := by
 funext s; simp [lazyDropWord,once_incomplete,sequence,pure_bind,lazyDrop]
#print axioms incomplete_drop_exact
theorem complete_drop_exact (f v : Op S Unit) (invalid : Op S LazyState) :
 lazyDropWord 0 f v invalid = v := by
 funext s; simp [lazyDropWord,once_complete,sequence,pure_bind,lazyDrop]
#print axioms complete_drop_exact
theorem poisoned_unwind_no_extra_effect (f v : Op S Unit)
 (invalid : Op S LazyState) (dp : Panic → Panic → Op S Unit)
 (p : Panic) (s : S) :
 unwind p (lazyDropWord 2 f v invalid) dp s = ⟨[],s,.panic p⟩ := by
 simp [poisoned_drop_exact,unwind,PV_DIAG3.pure,prepend]
#print axioms poisoned_unwind_no_extra_effect
end PV_DIAG4
