import KNA_Frame
set_option autoImplicit false
namespace KNA_Capacity
open KMX_CopyMeaning KMY_WindowComposition
theorem result (len size : Nat) :
 len≤max 8 (max (2*len) (len+size)) ∧
 len+size≤max 8 (max (2*len) (len+size)) := by omega
#print axioms result
end KNA_Capacity
