import KNA_Frame
set_option autoImplicit false
namespace KNA_Window00
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage answer : Nat → Nat) (j : Nat)
 (range : 0≤j ∧ j<160) :
 window answer (loop before garbage 0 (min 1736 3472)) 1736 32 j =
 if j<1736 then before j else answer (j-1736) :=
 KMZ_Growth.append_after_growth before garbage answer 1736 1736 3472 32 j
 (by omega) (by omega) (by omega)
#print axioms result
end KNA_Window00
