import NMC_ParentState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Parent
open Aeneas Aeneas.Std Result
/-- Exact disjoint frame, including allocated and unallocated old cells. -/
theorem write_frame (heap : Heap) (owner address : Nat) (value : Option Claims)
 (disjoint : address≠owner) : write heap owner value address=heap address := by
 simp only [write,if_neg disjoint]
theorem write_owner (heap : Heap) (owner : Nat) (value : Option Claims) :
 write heap owner value owner=value := by simp only [write,if_pos rfl]
/-- Installing the complete returned value and then releasing it does not
recover arbitrary stale bytes. Only other allocation identities are framed. -/
theorem release_frame (heap : Heap) (owner address : Nat) (value : Claims)
 (disjoint : address≠owner) :
 write (write heap owner (some value)) owner none address=heap address := by
 rw [write_frame _ _ _ _ disjoint,write_frame _ _ _ _ disjoint]
/-- Allocation identity never implies a data equality. Payload equality must
be delivered by the same child packet. -/
theorem owned_value (left right : OwnedClaims)
 (same : left=right) : left.identity=right.identity ∧ left.value=right.value :=
 ⟨congrArg OwnedClaims.identity same,congrArg OwnedClaims.value same⟩
#print axioms write_frame
#print axioms write_owner
#print axioms release_frame
#print axioms owned_value
end AspisR1.NMC_Parent
end
