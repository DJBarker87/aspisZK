import R1Z.PV_Inv_MaskFold
set_option autoImplicit false
namespace R1Z.PV_Inv_MaskRowFold

def rowBits (block : Nat) (rows : List Nat) : List Nat :=
  (rows.filter (fun row => decide (row / 16 = block))).map (fun row => row % 16)

def mask (block : Nat) (rows : List Nat) : Nat :=
  PV_Inv_MaskFold.bits 0 (rowBits block rows)

/-- Sorting and deduplication preserve the mask. The premise is set equality,
not enumeration equality; no permutation order is imposed on the native sort. -/
theorem set_transport (xs ys : List Nat) (members : ∀ row, row ∈ xs ↔ row ∈ ys)
    (block : Nat) : mask block xs = mask block ys := by
  apply Nat.eq_of_testBit_eq
  intro bit
  apply PV_Inv_MaskFold.order_irrelevant
  intro value
  simp only [rowBits,List.mem_map,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨row,⟨hr,hb⟩,hv⟩
    exact ⟨row,⟨(members row).mp hr,hb⟩,hv⟩
  · rintro ⟨row,⟨hr,hb⟩,hv⟩
    exact ⟨row,⟨(members row).mpr hr,hb⟩,hv⟩

#print axioms set_transport
end R1Z.PV_Inv_MaskRowFold
