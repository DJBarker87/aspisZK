import NCD_KMX_CopyMeaning
set_option autoImplicit false
namespace NCD_WindowPartition
/-- Every address of the full carrier lies in one bounded window, including
an incomplete final window. No concrete carrier is enumerated. -/
theorem partition (total k : Nat) (inside : k<total) :
    let base := k/32*32
    let len := min 32 (total-base)
    0<len ∧ len≤32 ∧ base+len≤total ∧ k%32<len ∧ base+k%32=k := by
  have width : k%32<32 := Nat.mod_lt k (by decide)
  have split := Nat.mod_add_div k 32
  have shape : k/32*32+k%32=k := by omega
  dsimp only
  omega

/-- The existing KMX value law supplies the disjoint exterior for one indexed
write after embedding its window offset in the same full storage carrier.
Native validity/provenance and the embedding itself remain P6 obligations. -/
theorem exterior {α : Type} (before : Nat → α) (value : α) (base i k : Nat)
    (other : k≠base+i) :
    KMX_CopyMeaning.loop (fun _ => value) before (base+i) 1 k=before k := by
  apply KMX_CopyMeaning.copy_frame
  omega

#print axioms partition
#print axioms exterior
end NCD_WindowPartition
