import KMZ_Growth
set_option autoImplicit false
namespace KMZ_IteratorSuffix
open KMX_CopyMeaning KMY_WindowComposition
theorem result {α : Type} (raw : Nat → α) (i j : Nat) (hi : i<63) (hj : j<63-i) :
 i+1+j<64 ∧ raw ((i+1)+j)=raw (i+(1+j)) := by
 constructor
 · omega
 · rw [Nat.add_assoc]
#print axioms result
end KMZ_IteratorSuffix
