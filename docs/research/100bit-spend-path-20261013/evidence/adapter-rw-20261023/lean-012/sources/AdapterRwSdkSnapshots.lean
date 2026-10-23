import AdapterRwRuntimeAdmission

/-! Entry snapshots use the existing SDK machine only. Native interpretation
still uses exactly S2TrustedSdkBorrow and a related initial native heap. -/
set_option autoImplicit false
namespace AspisR1.AdapterRw.Snapshots
open S2Trust

def sharedSnapshot {F : Type} (s : Heap F) (a t o : Nat) : Heap F :=
  (run (run s (.shared a t o)).1 (.drop t)).1

/-- A completed entry snapshot restores the heap, including counters and guards.
The owned payload copy is an independent value, not a live SDK guard. -/
theorem shared_snapshot_restores {F : Type} (s : Heap F) (a t o : Nat)
    (empty : s.guards = []) (zero : s.counter (s.accounts a).1 = 0) :
    sharedSnapshot s a t o = s := by
  have shared : run s (.shared a t o) =
      (acquire s (s.accounts a).1 t o .shared, .guard t) := by
    simp [run, zero, maxCounter]
  unfold sharedSnapshot
  rw [shared]
  simp only [run,lookup,acquire,List.find?_cons,beq_self_eq_true,↓reduceIte]
  simp only [release,acquire,empty,List.filter_cons,beq_self_eq_true,Bool.not_true,
    Bool.false_eq_true,↓reduceIte,List.filter_nil]
  have counters : put (put s.counter (s.accounts a).1 (s.counter (s.accounts a).1 + 1))
      (s.accounts a).1
      (put s.counter (s.accounts a).1 (s.counter (s.accounts a).1 + 1)
        (s.accounts a).1 - 1) = s.counter := by
    funext c
    by_cases same : c = (s.accounts a).1 <;> simp [put,same,zero]
  simp only [counters]
  cases s
  simp_all

/-- Every bounded snapshot can be sequenced: the next account sees the original
runtime admission, even when duplicate keys share a cell. -/
theorem entry_snapshot_restores {F : Type} {s : Heap F}
    {keys : Nat → List UInt8} {n a : Nat}
    (runtime : RuntimeEntrypointAdmission s keys n) (within : a < n) (t o : Nat) :
    sharedSnapshot s a t o = s :=
  shared_snapshot_restores s a t o runtime.freshGuards (runtime.counterZero a within)

#print axioms shared_snapshot_restores
#print axioms entry_snapshot_restores
end AspisR1.AdapterRw.Snapshots
