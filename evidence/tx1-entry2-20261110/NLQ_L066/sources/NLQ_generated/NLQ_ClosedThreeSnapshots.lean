import NLQ_ClosedSnapshotStep
set_option autoImplicit false
noncomputable section
namespace NLQ_ClosedThreeSnapshots
open Aeneas Aeneas.Std Result AspisR1.S2W_D189Entry AspisR1.S2Trust NLQ_ClosedSnapshotStep
/-- Three CLOSED callee uses on one SDK world chain, each at the restored
world of its predecessor. No independent successful borrow or fresh world. -/
theorem fold {W : Type} (e : Entry) (L : Library W (Nat → Record))
 (sdk : S2TrustedSdkBorrow L) (before : W) (related : L.related before e.heap)
 (valid : Valid e.heap) :
 ∃ first second third,
  Step e L before first 0 58295#usize 58295#usize ∧
  Step e L first second 1 1880#usize 1880#usize ∧
  Step e L second third 2 1768#usize 1768#usize ∧ L.related third e.heap := by
 obtain ⟨first,h1⟩ := at_site e L sdk before related valid 0 58295#usize 58295#usize
 obtain ⟨second,h2⟩ := at_site e L sdk first
  (related_after e L before first 0 58295#usize 58295#usize h1) valid 1 1880#usize 1880#usize
 obtain ⟨third,h3⟩ := at_site e L sdk second
  (related_after e L first second 1 1880#usize 1880#usize h2) valid 2 1768#usize 1768#usize
 exact ⟨first,second,third,h1,h2,h3,
  related_after e L second third 2 1768#usize 1768#usize h3⟩
#print fold
#print axioms fold
end NLQ_ClosedThreeSnapshots
