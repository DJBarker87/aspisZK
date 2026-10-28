import KNA_Frame
set_option autoImplicit false
namespace KNA_Query128
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage source : Nat → Nat) (i j : Nat)
 (domain : 1≤i ∧ i<16) (bound : j<64+4*i+4) :
 64+4*i+4≤128 ∧
 window source (loop before garbage 0 (min 128 128)) (64+4*i) 4 j =
 if j<64+4*i then before j else source (j-(64+4*i)) := by
 constructor
 · omega
 · exact KMZ_Growth.append_after_growth before garbage source (64+4*i) 128 128 4 j
     (by omega) (by omega) bound
#print axioms result
end KNA_Query128
