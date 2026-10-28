import KNA_Frame
import KMY_CheckpointComposition
set_option autoImplicit false
namespace KNA_LPm_K005
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage : Nat → Nat) (word : Nat) (len cap next j : Nat) (limit : len≤1732)
 (live : len≤cap) (growth : cap≤next) (bound : j<len+4) :
 len+4≤1736 ∧ window (fun b => (word / 2^(8*b)) % 256) (loop before garbage 0 (min cap next)) len 4 j =
 (if j<len then before j else (word / 2^(8*(j-len))) % 256) := by
 constructor
 · omega
 · exact KMZ_Growth.append_after_growth before garbage (fun b => (word / 2^(8*b)) % 256) len cap next 4 j live growth bound
#print axioms result
end KNA_LPm_K005
