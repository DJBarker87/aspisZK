import KNA_Frame
import KMY_CheckpointComposition
set_option autoImplicit false
namespace KNA_LPi_K013
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage : Nat → Nat) (limb : Nat → Nat) (len cap next j : Nat) (limit : len≤1704)
 (live : len≤cap) (growth : cap≤next) (bound : j<len+32) :
 len+32≤1736 ∧ window (fun b => (limb (b/4) / 2^(8*(b%4))) % 256) (loop before garbage 0 (min cap next)) len 32 j =
 (if j<len then before j else (limb ((j-len)/4) / 2^(8*((j-len)%4))) % 256) := by
 constructor
 · omega
 · exact KMZ_Growth.append_after_growth before garbage (fun b => (limb (b/4) / 2^(8*(b%4))) % 256) len cap next 32 j live growth bound
#print axioms result
end KNA_LPi_K013
