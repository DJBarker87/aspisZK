import KNA_Frame
import KMZ_LPf_K027
set_option autoImplicit false
namespace KNA_LPf_K027
open KMX_CopyMeaning KMY_WindowComposition
theorem result (initial garbage answer : Nat → Nat) (j : Nat) (bound : j<1768) :
 2+1=3 ∧ 1736+32=1768 ∧
 window answer (loop initial garbage 0 (min 1736 3472)) 1736 32 j =
 if j<1736 then initial j else answer (j-1736) := by
 refine ⟨by omega,by omega,?_⟩
 exact KMZ_LPf_K027.result initial garbage answer j bound
#print axioms result
end KNA_LPf_K027
