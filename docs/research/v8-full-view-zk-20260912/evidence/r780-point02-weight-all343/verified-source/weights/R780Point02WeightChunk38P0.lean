import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk05
import AspisV8R19.R780Point02WeightSharedChunk07
import AspisV8R19.R780Point02WeightSharedChunk08
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

namespace AspisV8R19.R780Point02WeightChunk38P0
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk05
open AspisV8R19.R780Point02WeightSharedChunk07
open AspisV8R19.R780Point02WeightSharedChunk08
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

theorem pw0_0376 : pw0 376 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 376 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather188]
  rw [hwe 188 (by omega), hwe 189 (by omega), hwo 188 (by omega)]
  change 7*w0 (2*188) + 5*(w0 (2*189)) - 5*w0 (2*188+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_376, w0_leaf_377, w0_leaf_378]
#print axioms pw0_0376

theorem pw0_0377 : pw0 377 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 377 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather188, gather188]
  rw [hwe 188 (by omega), hwe 190 (by omega), hwo 188 (by omega), hwo 189 (by omega)]
  change -5*(w0 (2*188) - (half*w0 (2*188) + half*w0 (2*190))) + 7*w0 (2*188+1) + 5*(w0 (2*189+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_376, w0_leaf_377, w0_leaf_379, w0_leaf_380]
#print axioms pw0_0377

theorem pw0_0378 : pw0 378 = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 378 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather189]
  rw [hwe 188 (by omega), hwe 189 (by omega), hwe 190 (by omega), hwo 189 (by omega)]
  change 7*w0 (2*189) + 5*(half^1*w0 (2*188) + half^1*w0 (2*190)) - 5*w0 (2*189+1) = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0)
  rw [w0_leaf_376, w0_leaf_378, w0_leaf_379, w0_leaf_380]
#print axioms pw0_0378

theorem pw0_0380 : pw0 380 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 380 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather190]
  rw [hwe 190 (by omega), hwe 191 (by omega), hwo 190 (by omega)]
  change 7*w0 (2*190) + 5*(w0 (2*191)) - 5*w0 (2*190+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_380, w0_leaf_381, w0_leaf_382]
#print axioms pw0_0380

theorem pw0_0381 : pw0 381 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^6*(0) + half^6*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 381 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather190, gather190]
  rw [hwe 128 (by omega), hwe 160 (by omega), hwe 176 (by omega), hwe 184 (by omega), hwe 188 (by omega), hwe 190 (by omega), hwe 192 (by omega), hwo 190 (by omega), hwo 191 (by omega)]
  change -5*(w0 (2*190) - (half*w0 (2*190) + half^2*w0 (2*188) + half^3*w0 (2*184) + half^4*w0 (2*176) + half^5*w0 (2*160) + half^6*w0 (2*128) + half^6*w0 (2*192))) + 7*w0 (2*190+1) + 5*(w0 (2*191+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^6*(0) + half^6*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_256, w0_leaf_320, w0_leaf_352, w0_leaf_368, w0_leaf_376, w0_leaf_380, w0_leaf_381, w0_leaf_383, w0_leaf_384]
#print axioms pw0_0381

theorem pw0_0382 : pw0 382 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^6*(0) + half^6*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 382 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather191]
  rw [hwe 128 (by omega), hwe 160 (by omega), hwe 176 (by omega), hwe 184 (by omega), hwe 188 (by omega), hwe 190 (by omega), hwe 191 (by omega), hwe 192 (by omega), hwo 191 (by omega)]
  change 7*w0 (2*191) + 5*(half^1*w0 (2*190) + half^2*w0 (2*188) + half^3*w0 (2*184) + half^4*w0 (2*176) + half^5*w0 (2*160) + half^6*w0 (2*128) + half^6*w0 (2*192)) - 5*w0 (2*191+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^6*(0) + half^6*(0)) - 5*(0)
  rw [w0_leaf_256, w0_leaf_320, w0_leaf_352, w0_leaf_368, w0_leaf_376, w0_leaf_380, w0_leaf_382, w0_leaf_383, w0_leaf_384]
#print axioms pw0_0382

theorem pw0_0496 : pw0 496 = 7*(([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, -2, -3, -1, 2, -2, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w0 7 5 (-5) 496 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather248]
  rw [hwe 248 (by omega), hwe 249 (by omega), hwo 248 (by omega)]
  change 7*w0 (2*248) + 5*(w0 (2*249)) - 5*w0 (2*248+1) = 7*(([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, -2, -3, -1, 2, -2, 1, 2] : List M).prod)
  rw [w0_leaf_496, w0_leaf_497, w0_leaf_498]
#print axioms pw0_0496

theorem pw0_0499 : pw0 499 = -5*((([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, -3, 2, 2, -2, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, -2, -3, -1, 2, -2, 1, 2] : List M).prod) + half^1*(([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w0 7 5 (-5) 499 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather249, gather249]
  rw [hwe 249 (by omega), hwe 251 (by omega), hwo 248 (by omega), hwo 249 (by omega), hwo 250 (by omega)]
  change -5*(w0 (2*249) - (half*w0 (2*249) + half*w0 (2*251))) + 7*w0 (2*249+1) + 5*(half^1*w0 (2*248+1) + half^1*w0 (2*250+1)) = -5*((([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, -3, 2, 2, -2, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, -2, -3, -1, 2, -2, 1, 2] : List M).prod) + half^1*(([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List M).prod))
  rw [w0_leaf_497, w0_leaf_498, w0_leaf_499, w0_leaf_501, w0_leaf_502]
#print axioms pw0_0499

end
end AspisV8R19.R780Point02WeightChunk38P0
