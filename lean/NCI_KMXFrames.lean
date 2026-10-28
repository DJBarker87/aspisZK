import KMX_CopyMeaning
set_option autoImplicit false
namespace AspisR1.NCI_KMXFrames

theorem window {α : Type} (src dst : Nat → α) (base width k : Nat) :
    KMX_CopyMeaning.loop (fun i => src (base+i)) dst 0 width k =
      if k<width then src (base+k) else dst k :=
  KMX_CopyMeaning.copy_prefix _ _ width k

theorem checkpoint_weights {α : Type} (src dst : Nat → α) (j k : Nat)
    (hj : j<64) (hk : k<16) :
    KMX_CopyMeaning.loop src dst 712 1024 (712+16*j+k)=src (712+16*j+k) := by
  rw [KMX_CopyMeaning.loop_spec]
  apply if_pos
  constructor <;> omega

theorem checkpoint_frame {α : Type} (src dst : Nat → α) (k : Nat)
    (outside : k<712 ∨ 1736≤k) :
    KMX_CopyMeaning.loop src dst 712 1024 k=dst k := by
  apply KMX_CopyMeaning.copy_frame
  omega

theorem disjoint {α : Type} (src1 src2 dst : Nat → α) (a n b m k : Nat)
    (separate : a+n≤b ∨ b+m≤a) :
    KMX_CopyMeaning.loop src2 (KMX_CopyMeaning.loop src1 dst a n) b m k=
      KMX_CopyMeaning.loop src1 (KMX_CopyMeaning.loop src2 dst b m) a n k := by
  simp only [KMX_CopyMeaning.loop_spec]
  by_cases first : a≤k ∧ k<a+n
  · by_cases second : b≤k ∧ k<b+m
    · omega
    · simp [first,second]
  · by_cases second : b≤k ∧ k<b+m <;> simp [first,second]
#print axioms window
#print axioms checkpoint_weights
#print axioms checkpoint_frame
#print axioms disjoint
end AspisR1.NCI_KMXFrames
