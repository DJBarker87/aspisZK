import NHJ_SdkValidity
set_option autoImplicit false
namespace NHJ_SdkBorrowPacket
open AspisR1.S2Trust

theorem returning_shared {W F : Type} (L : Library W F)
    (sdk : S2TrustedSdkBorrow L) (w : W) (s : Heap F)
    (related : L.related w s) (valid : Valid s) (a t o : Nat)
    (enabled : Enabled s (.shared a t o))
    (low : 0 ≤ s.counter (s.accounts a).1)
    (high : s.counter (s.accounts a).1 < maxCounter) :
    ∃ w1 w2 w3,
      L.run w (.shared a t o) = (w1,.guard t) ∧
      L.run w1 (.deref t) = (w2,.payload (s.payload (s.accounts a).1)) ∧
      L.run w2 (.drop t) = (w3,.unit) ∧ L.related w3 s := by
  let cell := (s.accounts a).1
  let s1 := acquire s cell t o .shared
  let g : Guard := ⟨t,cell,o,.shared,(s.payload cell).descriptor⟩
  have v1 : Valid s1 := NHJ_SdkValidity.acquired_valid s a t o valid enabled low high
  have found : lookup s1 t = some g := by simp [s1,g,lookup,acquire]
  have positive : 0 < s1.counter g.cell := by
    have positive' : 0 < s.counter (s.accounts a).1 + 1 := by omega
    simpa [s1,g,acquire,put,cell] using positive'
  obtain ⟨w1,run1,rel1⟩ := sdk.shared_ok w s a t o related valid enabled low high
  obtain ⟨w2,run2,rel2⟩ := sdk.shared_deref w1 s1 t g rel1 v1 found rfl
  obtain ⟨w3,run3,rel3⟩ := sdk.shared_drop w2 s1 t g rel2 v1 found rfl positive
  have released : release s1 g = s := NHJ_SdkBracket.shared_release s a t o enabled.2.1
  refine ⟨w1,w2,w3,run1,?_,run3,?_⟩
  · simpa [s1,acquire,g,cell] using run2
  · simpa [released] using rel3

theorem rejected_shared {W F : Type} (L : Library W F)
    (sdk : S2TrustedSdkBorrow L) (w : W) (s : Heap F)
    (related : L.related w s) (valid : Valid s) (a t o : Nat)
    (enabled : Enabled s (.shared a t o))
    (blocked : s.counter (s.accounts a).1 < 0 ∨ s.counter (s.accounts a).1 = maxCounter) :
    ∃ w', L.run w (.shared a t o) = (w',.borrowFailed) ∧ L.related w' s :=
  sdk.shared_err w s a t o related valid enabled blocked
#print axioms returning_shared
#print axioms rejected_shared
end NHJ_SdkBorrowPacket
