import NIM_NHJ_SnapshotPacket
set_option autoImplicit false
noncomputable section
namespace NHY_SnapshotRoot
open Aeneas Aeneas.Std Result
open AspisR1.S2W_D189Entry AspisR1.S2Trust

/-- Root-domain SDK law: no successful-borrow or parent-success premise. -/
theorem returning {W : Type} (e : Entry) (L : Library W (Nat → Record))
    (sdk : S2TrustedSdkBorrow L) (w : W) (related : L.related w e.heap)
    (valid : Valid e.heap) (a : Nat) :
    ∃ token owner w1 w2 w3,
      L.run w (.shared a token owner) = (w1,.guard token) ∧
      L.run w1 (.deref token) = (w2,.payload (e.heap.payload (e.heap.accounts a).1)) ∧
      L.run w2 (.drop token) = (w3,.unit) ∧ L.related w3 e.heap := by
  obtain ⟨token,owner,enabled⟩ := NHJ_SdkDomains.enabled_exists e.heap a rfl
  obtain ⟨w1,w2,w3,h1,h2,h3,h4⟩ :=
    NHJ_SdkBorrowPacket.returning_shared L sdk w e.heap related valid a token owner enabled
      (by change (0 : Int) ≤ 0; omega)
      (by change (0 : Int) < maxCounter; unfold maxCounter; omega)
  exact ⟨token,owner,w1,w2,w3,h1,h2,h3,h4⟩

/-- Both-arm selector is the exact SDK reply. The Err arm is ruled out by the
computed entry heap, rather than by a caller-provided success hypothesis. -/
theorem root_not_blocked (e : Entry) (a : Nat) :
    ¬ (e.heap.counter (e.heap.accounts a).1 < 0 ∨
       e.heap.counter (e.heap.accounts a).1 = maxCounter) := by
  change ¬ ((0 : Int) < 0 ∨ (0 : Int) = maxCounter)
  unfold maxCounter
  omega

#print axioms returning
#print axioms root_not_blocked
end NHY_SnapshotRoot
