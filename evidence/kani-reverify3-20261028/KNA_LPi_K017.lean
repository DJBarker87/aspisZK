import KNA_Frame
import KMZ_LPi_K017
set_option autoImplicit false
namespace KNA_LPi_K017
open KMX_CopyMeaning KMY_WindowComposition
theorem result (body garbage hp hu answer : Nat → Nat) (j : Nat) (bound : j<1768) :
 0+3=3 ∧ 1736+32=1768 ∧
 window answer (loop (KMZ_LPi_K017.joinedPrefix body hp hu) garbage 0 (min 1736 3472)) 1736 32 j =
 if 16≤j ∧ j<48 then hp (j-16) else if 48≤j ∧ j<80 then hu (j-48)
 else if j<1736 then body j else if j<1768 then answer (j-1736) else body j := by
 refine ⟨by omega,by omega,?_⟩
 exact KMZ_LPi_K017.result body garbage hp hu answer j bound
#print axioms result
end KNA_LPi_K017
