import KNA_Frame
set_option autoImplicit false
namespace KNA_Query256
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage source : Nat → Nat) (i j : Nat)
 (domain : 17≤i ∧ i<22) (bound : j<64+4*i+4) :
 64+4*i+4≤256 ∧
 window source (loop before garbage 0 (min 256 256)) (64+4*i) 4 j =
 if j<64+4*i then before j else source (j-(64+4*i)) := by
 constructor
 · omega
 · exact KMZ_Growth.append_after_growth before garbage source (64+4*i) 256 256 4 j
     (by omega) (by omega) bound
#print axioms result
end KNA_Query256
