import R1Z.PV_CB3_TransportNodup
set_option autoImplicit false
namespace R1Z.PV_CB3_TransportPermutation
open PV_CB3_TransportOrder

theorem perm (pivot : Nat) (pads : List Nat) (hn : pads.Nodup)
    (hp : ∀ r, r ∈ pads → r < pivot) : (order pivot pads).Perm (List.range (pivot+1)) := by
  apply List.perm_iff_count.mpr
  intro a
  rw [(PV_CB3_TransportNodup.order_nodup pivot pads hn hp).count,List.nodup_range.count]
  simp only [PV_CB3_TransportMembership.range_membership pivot pads hp a]

theorem length (pivot : Nat) (pads : List Nat) (hn : pads.Nodup)
    (hp : ∀ r, r ∈ pads → r < pivot) : (order pivot pads).length = pivot+1 := by
  have h := (perm pivot pads hn hp).length_eq
  simpa only [List.length_range] using h

theorem read_bound (pads : List Nat) (hn : pads.Nodup)
    (hp : ∀ r, r ∈ pads → r < 1023) (j : Nat) (hj : j < 1024) :
    (order 1023 pads)[j]'(by rw [length 1023 pads hn hp]; exact hj) < 1024 := by
  apply semantic_row_bound pads hp
  exact List.getElem_mem _
#print axioms perm
#print axioms length
#print axioms read_bound
end R1Z.PV_CB3_TransportPermutation
