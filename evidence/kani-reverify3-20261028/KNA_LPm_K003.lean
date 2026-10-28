import KNA_Frame
import KMY_CheckpointComposition
set_option autoImplicit false
namespace KNA_LPm_K003
open KMX_CopyMeaning KMY_WindowComposition
theorem result (before garbage : Nat → Nat) (limb : Nat → Nat) (i cap next j : Nat) (idx : i<64)
 (live : (712+16*i)≤cap) (growth : cap≤next) (bound : j<(712+16*i)+16) :
 (712+16*i)+16≤1736 ∧ window (fun b => (limb (b/4) / 2^(8*(b%4))) % 256) (loop before garbage 0 (min cap next)) (712+16*i) 16 j =
 (if j<(712+16*i) then before j else (limb ((j-(712+16*i))/4) / 2^(8*((j-(712+16*i))%4))) % 256) := by
 constructor
 · omega
 · exact KMZ_Growth.append_after_growth before garbage (fun b => (limb (b/4) / 2^(8*(b%4))) % 256) (712+16*i) cap next 16 j live growth bound
#print axioms result
end KNA_LPm_K003
