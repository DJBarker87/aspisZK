import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk00
import AspisV8R19.R780Point02WeightSharedChunk05
import AspisV8R19.R780Point02WeightSharedChunk09
import AspisV8R19.R780Point02WeightSharedChunk10
import AspisV8R19.R748FiniteGatherSchedules
import AspisV8R19.R748SchedulePrototype
import AspisV8R19.R748GatherLoop00
import AspisV8R19.R748GatherLoop01
import AspisV8R19.R748GatherLoop02
import AspisV8R19.R748GatherLoop03
import AspisV8R19.R748GatherLoop04
import AspisV8R19.R748GatherLoop05
import AspisV8R19.R748GatherLoop06
import AspisV8R19.R748GatherLoop07
import AspisV8R19.R748GatherExpand00
import AspisV8R19.R748GatherExpand01
import AspisV8R19.R748GatherExpand02
import AspisV8R19.R748GatherExpand03
import AspisV8R19.R748GatherExpand04
import AspisV8R19.R748GatherExpand05
import AspisV8R19.R748GatherExpand06
import AspisV8R19.R748GatherExpand07
import AspisV8R19.R748GatherNested00
import AspisV8R19.R748GatherNested01
import AspisV8R19.R748GatherNested02
import AspisV8R19.R748GatherNested03
import AspisV8R19.R748GatherNested04

namespace AspisV8R19.R780Point02WeightChunk39P0
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk00
open AspisV8R19.R780Point02WeightSharedChunk05
open AspisV8R19.R780Point02WeightSharedChunk09
open AspisV8R19.R780Point02WeightSharedChunk10
open AspisV8R17
open AspisV8R19.R742SourceObservationHom
open AspisV8R19.R748FiniteGatherSchedules
open AspisV8R19.R748SchedulePrototype
open AspisV8R19.R748GatherExpand00
open AspisV8R19.R748GatherExpand01
open AspisV8R19.R748GatherExpand02
open AspisV8R19.R748GatherExpand03
open AspisV8R19.R748GatherExpand04
open AspisV8R19.R748GatherExpand05
open AspisV8R19.R748GatherExpand06
open AspisV8R19.R748GatherExpand07
open AspisV8R19.R748GatherNested00
open AspisV8R19.R748GatherNested01
open AspisV8R19.R748GatherNested02
open AspisV8R19.R748GatherNested03
open AspisV8R19.R748GatherNested04
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096

theorem pw0_0500 : pw0 500 = 7*(([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w0 7 5 (-5) 500 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather250]
  rw [hwe 250 (by omega), hwe 251 (by omega), hwo 250 (by omega)]
  change 7*w0 (2*250) + 5*(w0 (2*251)) - 5*w0 (2*250+1) = 7*(([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List M).prod)
  rw [w0_leaf_500, w0_leaf_501, w0_leaf_502]
#print axioms pw0_0500

theorem pw0_0501 : pw0 501 = -5*((([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, -2, 4, 2, 2, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w0 7 5 (-5) 501 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather250, gather250]
  rw [hwe 248 (by omega), hwe 250 (by omega), hwe 252 (by omega), hwo 250 (by omega), hwo 251 (by omega)]
  change -5*(w0 (2*250) - (half*w0 (2*250) + half^2*w0 (2*248) + half^2*w0 (2*252))) + 7*w0 (2*250+1) + 5*(w0 (2*251+1)) = -5*((([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, -2, 4, 2, 2, -2, 1, 2] : List M).prod))
  rw [w0_leaf_496, w0_leaf_500, w0_leaf_501, w0_leaf_503, w0_leaf_504]
#print axioms pw0_0501

theorem pw0_0503 : pw0 503 = -5*((([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, 4, 2, 2, -2, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List M).prod) + half^2*(([1, 1, 2, -2, -3, -1, 2, -2, 1, 2] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w0 7 5 (-5) 503 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather251, gather251]
  rw [hwe 249 (by omega), hwe 251 (by omega), hwe 253 (by omega), hwo 248 (by omega), hwo 250 (by omega), hwo 251 (by omega), hwo 252 (by omega)]
  change -5*(w0 (2*251) - (half*w0 (2*251) + half^2*w0 (2*249) + half^2*w0 (2*253))) + 7*w0 (2*251+1) + 5*(half^1*w0 (2*250+1) + half^2*w0 (2*248+1) + half^2*w0 (2*252+1)) = -5*((([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, 4, 2, 2, -2, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List M).prod) + half^2*(([1, 1, 2, -2, -3, -1, 2, -2, 1, 2] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod))
  rw [w0_leaf_497, w0_leaf_498, w0_leaf_501, w0_leaf_502, w0_leaf_503, w0_leaf_505, w0_leaf_506]
#print axioms pw0_0503

theorem pw0_0504 : pw0 504 = 7*(([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w0 7 5 (-5) 504 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather252]
  rw [hwe 252 (by omega), hwe 253 (by omega), hwo 252 (by omega)]
  change 7*w0 (2*252) + 5*(w0 (2*253)) - 5*w0 (2*252+1) = 7*(([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod)
  rw [w0_leaf_504, w0_leaf_505, w0_leaf_506]
#print axioms pw0_0504

theorem pw0_0505 : pw0 505 = -5*((([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, 3, -3, 2, 2, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w0 7 5 (-5) 505 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather252, gather252]
  rw [hwe 252 (by omega), hwe 254 (by omega), hwo 252 (by omega), hwo 253 (by omega)]
  change -5*(w0 (2*252) - (half*w0 (2*252) + half*w0 (2*254))) + 7*w0 (2*252+1) + 5*(w0 (2*253+1)) = -5*((([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, 3, -3, 2, 2, -2, 1, 2] : List M).prod))
  rw [w0_leaf_504, w0_leaf_505, w0_leaf_507, w0_leaf_508]
#print axioms pw0_0505

theorem pw0_0507 : pw0 507 = -5*((([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, 3, -3, 2, 2, -2, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod) + half^1*(([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w0 7 5 (-5) 507 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather253, gather253]
  rw [hwe 253 (by omega), hwe 255 (by omega), hwo 252 (by omega), hwo 253 (by omega), hwo 254 (by omega)]
  change -5*(w0 (2*253) - (half*w0 (2*253) + half*w0 (2*255))) + 7*w0 (2*253+1) + 5*(half^1*w0 (2*252+1) + half^1*w0 (2*254+1)) = -5*((([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, 3, -3, 2, 2, -2, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod) + half^1*(([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List M).prod))
  rw [w0_leaf_505, w0_leaf_506, w0_leaf_507, w0_leaf_509, w0_leaf_510]
#print axioms pw0_0507

theorem pw0_0508 : pw0 508 = 7*(([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w0 7 5 (-5) 508 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather254]
  rw [hwe 254 (by omega), hwe 255 (by omega), hwo 254 (by omega)]
  change 7*w0 (2*254) + 5*(w0 (2*255)) - 5*w0 (2*254+1) = 7*(([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List M).prod)
  rw [w0_leaf_508, w0_leaf_509, w0_leaf_510]
#print axioms pw0_0508

theorem pw0_0509 : pw0 509 = -5*((([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List M).prod) + half^4*(([1, 1, -1, -2, -3, -1, 2, -2, 1, -1] : List M).prod) + half^5*(0) + half^6*(0) + half^7*(0) + half^8*(0) + half^8*(0))) + 7*(([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, 3, 4, 2, 2, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w0 7 5 (-5) 509 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather254, gather254]
  rw [hwe 0 (by omega), hwe 128 (by omega), hwe 192 (by omega), hwe 224 (by omega), hwe 240 (by omega), hwe 248 (by omega), hwe 252 (by omega), hwe 254 (by omega), hwe 256 (by omega), hwo 254 (by omega), hwo 255 (by omega)]
  change -5*(w0 (2*254) - (half*w0 (2*254) + half^2*w0 (2*252) + half^3*w0 (2*248) + half^4*w0 (2*240) + half^5*w0 (2*224) + half^6*w0 (2*192) + half^7*w0 (2*128) + half^8*w0 (2*0) + half^8*w0 (2*256))) + 7*w0 (2*254+1) + 5*(w0 (2*255+1)) = -5*((([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List M).prod) + half^4*(([1, 1, -1, -2, -3, -1, 2, -2, 1, -1] : List M).prod) + half^5*(0) + half^6*(0) + half^7*(0) + half^8*(0) + half^8*(0))) + 7*(([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, 3, 4, 2, 2, -2, 1, 2] : List M).prod))
  rw [w0_leaf_0, w0_leaf_256, w0_leaf_384, w0_leaf_448, w0_leaf_480, w0_leaf_496, w0_leaf_504, w0_leaf_508, w0_leaf_509, w0_leaf_511, w0_leaf_512]
#print axioms pw0_0509

end
end AspisV8R19.R780Point02WeightChunk39P0
