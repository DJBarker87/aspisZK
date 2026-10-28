import KNA_Frame
set_option autoImplicit false
namespace KNA_Partition
open KMX_CopyMeaning KMY_WindowComposition
theorem result (j : Nat) (h : j<1768) :
 (j<1736 ∧ ∃ w, w<11 ∧ 160*w≤j ∧ j<min 1736 (160*(w+1))) ∨
 (1736≤j ∧ j<1768) := by
 by_cases p : j<1736
 · left
   refine ⟨p,j/160,?_,?_,?_⟩
   · omega
   · omega
   · omega
 · right; omega
#print axioms result
end KNA_Partition
