import S2W_D189Consolidation
set_option autoImplicit false
namespace AspisR1.NIS_AdmissionSdk
open S2Trust S2W_D189Entry S2W_D189Consolidation

/-- These are applications of the headline's named runtime contract, not
native implementations of the runtime's admission predicates. -/
theorem fresh {W : Type} (L : Library W (Nat → Record)) (e : Entry) (w : W)
    (n t o : Nat) (admission : RuntimeEntrypointAdmission L e w n) :
    Fresh e.heap t o := by
  constructor
  · simp only [lookup, admission.entry.freshGuards, List.find?_nil]
  · intro g member
    rw [admission.entry.freshGuards] at member
    cases member

theorem enabled {W : Type} (L : Library W (Nat → Record)) (e : Entry) (w : W)
    (n a t o : Nat) (admission : RuntimeEntrypointAdmission L e w n) (within : a < n) :
    Enabled e.heap (.shared a t o) ∧ Enabled e.heap (.exclusive a t o) := by
  have ready := fresh L e w n t o admission
  exact ⟨⟨admission.entry.liveAccount a within,ready⟩,
    ⟨admission.entry.liveAccount a within,ready⟩⟩

theorem shared {W : Type} (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (e : Entry) (w : W) (n a t o : Nat)
    (admission : RuntimeEntrypointAdmission L e w n) (within : a < n) :
    Matches L w (.shared a t o)
      (acquire e.heap (e.heap.accounts a).1 t o .shared,.guard t) := by
  apply sdk.shared_ok w e.heap a t o admission.related admission.entry.valid
    (enabled L e w n a t o admission within).1
  · rw [admission.entry.counterZero a within]
  · rw [admission.entry.counterZero a within]
    simp only [maxCounter]
    omega

theorem exclusive {W : Type} (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (e : Entry) (w : W) (n a t o : Nat)
    (admission : RuntimeEntrypointAdmission L e w n) (within : a < n) :
    Matches L w (.exclusive a t o)
      (acquire e.heap (e.heap.accounts a).1 t o .exclusive,.guard t) :=
  sdk.exclusive_ok w e.heap a t o admission.related admission.entry.valid
    (enabled L e w n a t o admission within).2 (admission.entry.counterZero a within)

#print axioms fresh
#print axioms enabled
#print axioms shared
#print axioms exclusive
end AspisR1.NIS_AdmissionSdk
