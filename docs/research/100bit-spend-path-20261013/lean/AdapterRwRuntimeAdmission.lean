import S2TrustedSdkBorrow

/-! D183 runtime-entry premise. This is independent of adapter acceptance.
Its SDK/runtime source check is runtime-source-check.json. It does not establish
allocator/CU admission, native interpretation, inter-transaction retention or ROM.
No existing SDK trust field is changed. -/
set_option autoImplicit false
namespace AspisR1.AdapterRw
open S2Trust

structure RuntimeEntrypointAdmission {F : Type} (s : Heap F)
    (keys : Nat → List UInt8) (accountCount : Nat) : Prop where
  valid : Valid s
  freshGuards : s.guards = []
  noExternalBorrows : ∀ c, s.external c = 0
  liveAccount : ∀ a, a < accountCount → s.ownerLive a = true
  counterZero : ∀ a, a < accountCount → s.counter (s.accounts a).1 = 0
  sharedCellsOnlyEqualKeys : ∀ a b, a < accountCount → b < accountCount →
    (s.accounts a).1 = (s.accounts b).1 → keys a = keys b
  duplicateKeysShareCell : ∀ a b, a < accountCount → b < accountCount →
    keys a = keys b → (s.accounts a).1 = (s.accounts b).1

theorem distinct_keys_distinct_cells {F : Type} {s : Heap F}
    {keys : Nat → List UInt8} {n a b : Nat}
    (runtime : RuntimeEntrypointAdmission s keys n)
    (ha : a < n) (hb : b < n) (different : keys a ≠ keys b) :
    (s.accounts a).1 ≠ (s.accounts b).1 := by
  intro same
  exact different (runtime.sharedCellsOnlyEqualKeys a b ha hb same)

theorem entry_shared_available {F : Type} {s : Heap F}
    {keys : Nat → List UInt8} {n a t o : Nat}
    (runtime : RuntimeEntrypointAdmission s keys n) (ha : a < n) :
    (run s (.shared a t o)).2 = .guard t := by
  simp [run, runtime.counterZero a ha, maxCounter]

theorem entry_exclusive_available {F : Type} {s : Heap F}
    {keys : Nat → List UInt8} {n a t o : Nat}
    (runtime : RuntimeEntrypointAdmission s keys n) (ha : a < n) :
    (run s (.exclusive a t o)).2 = .guard t := by
  simp only [run, runtime.counterZero a ha, ↓reduceIte]

#print axioms distinct_keys_distinct_cells
#print axioms entry_shared_available
#print axioms entry_exclusive_available
end AspisR1.AdapterRw
