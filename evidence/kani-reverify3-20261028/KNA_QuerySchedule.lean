import KNA_Query128
import KNA_Query256
set_option autoImplicit false
namespace KNA_QuerySchedule
open KMX_CopyMeaning KMY_WindowComposition
theorem result (i : Nat) (h : i<22) :
 i=0 ∨ (1≤i ∧ i<16) ∨ i=16 ∨ (17≤i ∧ i<22) := by omega
#print axioms result
end KNA_QuerySchedule
