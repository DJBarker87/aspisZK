import KNA_Partition
set_option autoImplicit false
namespace KNA_FrameUnion
open KMX_CopyMeaning KMY_WindowComposition
theorem result (actual expected : Nat → Nat)
 (prefixWindows : ∀ w, w<11 → ∀ j, 160*w≤j → j<min 1736 (160*(w+1)) → actual j=expected j)
 (appended : ∀ j, 1736≤j → j<1768 → actual j=expected j) :
 ∀ j, j<1768 → actual j=expected j := by
 intro j bound
 rcases KNA_Partition.result j bound with ⟨_,w,hw,lo,hi⟩ | ⟨lo,hi⟩
 · exact prefixWindows w hw j lo hi
 · exact appended j lo hi
#print axioms result
end KNA_FrameUnion
