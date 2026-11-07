import NMX_R2_DistinctCanonical
set_option autoImplicit false
namespace NMX_R2_DistinctMap
open Aeneas Aeneas.Std AdapterRw NMX_R2_Carrier
/-- The complete 32-byte key carrier preserves pairwise inequality. -/
theorem pairwise (xs : List r1_pool_adapter.owned.OwnedAccount) :
 (xs.map account).Pairwise (fun a b => a.key ≠ b.key) ↔
 xs.Pairwise (fun a b => a.key ≠ b.key) := by
 rw [List.pairwise_map]
 simp only [account,ne_eq,NMX_R2_KeyCarrier.key_equal]
#print axioms pairwise
end NMX_R2_DistinctMap
