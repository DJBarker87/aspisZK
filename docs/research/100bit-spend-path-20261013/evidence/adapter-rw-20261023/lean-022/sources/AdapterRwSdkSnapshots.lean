import AdapterRwRuntimeAdmission

/-! Entry snapshots use the existing SDK machine only. Native interpretation
still uses exactly S2TrustedSdkBorrow and a related initial native heap. -/
set_option autoImplicit false
namespace AspisR1.AdapterRw.Snapshots
open S2Trust

def sharedBracket {F : Type} (s : Heap F) (a t o : Nat) : Heap F :=
  (run (run s (.shared a t o)).1 (.drop t)).1

/-- The acquire/drop bracket restores the heap, including counters and guards.
Owned-copy allocation occurs between these operations and is NOT modeled here. -/
theorem shared_bracket_restores {F : Type} (s : Heap F) (a t o : Nat)
    (empty : s.guards = []) (zero : s.counter (s.accounts a).1 = 0) :
    sharedBracket s a t o = s := by
  have shared : run s (.shared a t o) =
      (acquire s (s.accounts a).1 t o .shared, .guard t) := by
    simp [run, zero, maxCounter]
  unfold sharedBracket
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

/-- Borrow brackets can be sequenced even when duplicate keys share a cell.
Intervening allocation/copy effects need their separate native interpretation. -/
theorem entry_bracket_restores {F : Type} {s : Heap F}
    {keys : Nat → List UInt8} {n a : Nat}
    (runtime : RuntimeEntrypointAdmission s keys n) (within : a < n) (t o : Nat) :
    sharedBracket s a t o = s :=
  shared_bracket_restores s a t o runtime.freshGuards (runtime.counterZero a within)

/-- Admission of the temporary shared guard follows from runtime entry facts. -/
theorem acquired_valid {F : Type} {s : Heap F}
    {keys : Nat → List UInt8} {n a : Nat}
    (runtime : RuntimeEntrypointAdmission s keys n) (within : a < n) (t o : Nat) :
    Valid (acquire s (s.accounts a).1 t o .shared) := by
  rcases runtime.valid with ⟨_, bounds, _, live⟩
  refine ⟨by simp [acquire,runtime.freshGuards], ?_, ?_, live⟩
  · intro c
    have old := bounds c
    have external := runtime.noExternalBorrows c
    by_cases same : c = (s.accounts a).1
    · subst c
      simp [acquire,put,count,runtime.freshGuards,runtime.counterZero a within,
        runtime.noExternalBorrows,maxCounter,minCounter]
    · simpa [acquire,put,count,runtime.freshGuards,same,Ne.symm same,external]
        using old
  · intro g member
    simp only [acquire,runtime.freshGuards,List.mem_cons,List.not_mem_nil,or_false] at member
    subst g
    exact ⟨(live a (runtime.liveAccount a within)).2,rfl⟩

/-- An actual native acquisition is licensed using only the existing SDK trust. -/
theorem native_entry_shared {W F : Type} (L : Library W F)
    (trust : S2TrustedSdkBorrow L) (w : W) (s : Heap F)
    (keys : Nat → List UInt8) (n a t o : Nat)
    (runtime : RuntimeEntrypointAdmission s keys n) (within : a < n)
    (related : L.related w s) :
    Matches L w (.shared a t o)
      (acquire s (s.accounts a).1 t o .shared, .guard t) := by
  apply trust.shared_ok w s a t o related runtime.valid
  · exact ⟨runtime.liveAccount a within, by simp [Fresh,lookup,runtime.freshGuards]⟩
  · rw [runtime.counterZero a within]; exact Int.le_refl 0
  · rw [runtime.counterZero a within]; simp [maxCounter]

/-- The trusted dereference exposes exactly the entry account's payload. -/
theorem native_entry_read {W F : Type} (L : Library W F)
    (trust : S2TrustedSdkBorrow L) (w : W) (s : Heap F)
    (keys : Nat → List UInt8) (n a t o : Nat)
    (runtime : RuntimeEntrypointAdmission s keys n) (within : a < n)
    (related : L.related w (acquire s (s.accounts a).1 t o .shared)) :
    Matches L w (.deref t)
      (acquire s (s.accounts a).1 t o .shared, .payload (s.payload (s.accounts a).1)) := by
  apply trust.shared_deref w _ t
    ⟨t,(s.accounts a).1,o,.shared,(s.payload (s.accounts a).1).descriptor⟩
    related (acquired_valid runtime within t o)
  · simp [lookup,acquire]
  · rfl

/-- Return to the SAME entry heap after the actual guard drop. Intervening owned
allocation effects are a separate source boundary; this lemma assumes relatedness
at the drop cut and does not derive it by treating allocation as inert. -/
theorem native_entry_drop {W F : Type} (L : Library W F)
    (trust : S2TrustedSdkBorrow L) (w : W) (s : Heap F)
    (keys : Nat → List UInt8) (n a t o : Nat)
    (runtime : RuntimeEntrypointAdmission s keys n) (within : a < n)
    (related : L.related w (acquire s (s.accounts a).1 t o .shared)) :
    Matches L w (.drop t) (s, .unit) := by
  have dropped := trust.shared_drop w (acquire s (s.accounts a).1 t o .shared) t
    ⟨t,(s.accounts a).1,o,.shared,(s.payload (s.accounts a).1).descriptor⟩
    related (acquired_valid runtime within t o)
    (by simp [lookup,acquire]) rfl (by simp [acquire,put,runtime.counterZero a within])
  have restored := entry_bracket_restores runtime within t o
  unfold sharedBracket at restored
  have shared : run s (.shared a t o) =
      (acquire s (s.accounts a).1 t o .shared, .guard t) := by
    simp [run,runtime.counterZero a within,maxCounter]
  rw [shared] at restored
  simp only [run,lookup,acquire,List.find?_cons,beq_self_eq_true,↓reduceIte] at restored
  rw [restored] at dropped
  exact dropped

#print axioms shared_bracket_restores
#print axioms entry_bracket_restores
#print axioms acquired_valid
#print axioms native_entry_shared
#print axioms native_entry_read
#print axioms native_entry_drop
end AspisR1.AdapterRw.Snapshots
