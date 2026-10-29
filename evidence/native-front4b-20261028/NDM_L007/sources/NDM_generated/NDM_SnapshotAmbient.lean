import AdapterRwSdkSnapshots
set_option autoImplicit false
namespace NDM_SnapshotAmbient
open AspisR1 AspisR1.S2Trust AspisR1.AdapterRw

def ambient {F : Type} (s : Heap F) (f : F) : Heap F := {s with ambient := f}

theorem valid {F : Type} (s : Heap F) (f : F) : Valid (ambient s f) ↔ Valid s := Iff.rfl

theorem acquire_commutes {F : Type} (s : Heap F) (f : F) (c t o : Nat) (k : Kind) :
 ambient (acquire s c t o k) f = acquire (ambient s f) c t o k := rfl

theorem release_commutes {F : Type} (s : Heap F) (f : F) (g : Guard) :
 ambient (release s g) f = release (ambient s f) g := rfl

theorem runtime {F : Type} (s : Heap F) (f : F) (keys : Nat → List UInt8) (n : Nat)
 (h : RuntimeEntrypointAdmission s keys n) : RuntimeEntrypointAdmission (ambient s f) keys n :=
 ⟨h.valid,h.freshGuards,h.noExternalBorrows,h.liveAccount,h.counterZero,
 h.sharedCellsOnlyEqualKeys,h.duplicateKeysShareCell⟩

/-- Allocation can change ambient state. The native relatedness at this cut is NOT proved here. -/
theorem drop_after_ambient {W F : Type} (L : Library W F) (trust : S2TrustedSdkBorrow L)
 (w : W) (s : Heap F) (f : F) (keys : Nat → List UInt8) (n a t o : Nat)
 (h : RuntimeEntrypointAdmission s keys n) (within : a<n)
 (allocationCut : L.related w (ambient (acquire s (s.accounts a).1 t o .shared) f)) :
 Matches L w (.drop t) (ambient s f,.unit) := by
 exact Snapshots.native_entry_drop L trust w (ambient s f) keys n a t o
  (runtime s f keys n h) within allocationCut

/-- The account payload survives an ambient-only allocation cut exactly. -/
theorem payload {F : Type} (s : Heap F) (f : F) (c : Nat) :
 (ambient s f).payload c = s.payload c := rfl

#print axioms valid
#print axioms acquire_commutes
#print axioms release_commutes
#print axioms runtime
#print axioms drop_after_ambient
#print axioms payload
end NDM_SnapshotAmbient
