import KNA_Frame
set_option autoImplicit false
namespace KNA_LPf_K027
open KMX_CopyMeaning KMY_WindowComposition

theorem result (initial garbage answer : Nat → Nat) (j : Nat) (h : j<1768) :
 window answer (loop initial garbage 0 (min 1736 3472)) 1736 32 j =
 if j<1736 then initial j else answer (j-1736) :=
 KMZ_Growth.append_after_growth initial garbage answer 1736 1736 3472 32 j
  (by omega) (by omega) (by omega)
#print axioms result
end KNA_LPf_K027
