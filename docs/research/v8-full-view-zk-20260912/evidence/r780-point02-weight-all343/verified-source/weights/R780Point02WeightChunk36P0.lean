import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk08
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

namespace AspisV8R19.R780Point02WeightChunk36P0
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk08
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

theorem pw0_0352 : pw0 352 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 352 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather176]
  rw [hwe 176 (by omega), hwe 177 (by omega), hwo 176 (by omega)]
  change 7*w0 (2*176) + 5*(w0 (2*177)) - 5*w0 (2*176+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_352, w0_leaf_353, w0_leaf_354]
#print axioms pw0_0352

theorem pw0_0353 : pw0 353 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 353 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather176, gather176]
  rw [hwe 176 (by omega), hwe 178 (by omega), hwo 176 (by omega), hwo 177 (by omega)]
  change -5*(w0 (2*176) - (half*w0 (2*176) + half*w0 (2*178))) + 7*w0 (2*176+1) + 5*(w0 (2*177+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_352, w0_leaf_353, w0_leaf_355, w0_leaf_356]
#print axioms pw0_0353

theorem pw0_0355 : pw0 355 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 355 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather177, gather177]
  rw [hwe 177 (by omega), hwe 179 (by omega), hwo 176 (by omega), hwo 177 (by omega), hwo 178 (by omega)]
  change -5*(w0 (2*177) - (half*w0 (2*177) + half*w0 (2*179))) + 7*w0 (2*177+1) + 5*(half^1*w0 (2*176+1) + half^1*w0 (2*178+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0))
  rw [w0_leaf_353, w0_leaf_354, w0_leaf_355, w0_leaf_357, w0_leaf_358]
#print axioms pw0_0355

theorem pw0_0356 : pw0 356 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 356 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather178]
  rw [hwe 178 (by omega), hwe 179 (by omega), hwo 178 (by omega)]
  change 7*w0 (2*178) + 5*(w0 (2*179)) - 5*w0 (2*178+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_356, w0_leaf_357, w0_leaf_358]
#print axioms pw0_0356

theorem pw0_0357 : pw0 357 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 357 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather178, gather178]
  rw [hwe 176 (by omega), hwe 178 (by omega), hwe 180 (by omega), hwo 178 (by omega), hwo 179 (by omega)]
  change -5*(w0 (2*178) - (half*w0 (2*178) + half^2*w0 (2*176) + half^2*w0 (2*180))) + 7*w0 (2*178+1) + 5*(w0 (2*179+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_352, w0_leaf_356, w0_leaf_357, w0_leaf_359, w0_leaf_360]
#print axioms pw0_0357

theorem pw0_0359 : pw0 359 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 359 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather179, gather179]
  rw [hwe 177 (by omega), hwe 179 (by omega), hwe 181 (by omega), hwo 176 (by omega), hwo 178 (by omega), hwo 179 (by omega), hwo 180 (by omega)]
  change -5*(w0 (2*179) - (half*w0 (2*179) + half^2*w0 (2*177) + half^2*w0 (2*181))) + 7*w0 (2*179+1) + 5*(half^1*w0 (2*178+1) + half^2*w0 (2*176+1) + half^2*w0 (2*180+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0))
  rw [w0_leaf_353, w0_leaf_354, w0_leaf_357, w0_leaf_358, w0_leaf_359, w0_leaf_361, w0_leaf_362]
#print axioms pw0_0359

theorem pw0_0360 : pw0 360 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 360 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather180]
  rw [hwe 180 (by omega), hwe 181 (by omega), hwo 180 (by omega)]
  change 7*w0 (2*180) + 5*(w0 (2*181)) - 5*w0 (2*180+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_360, w0_leaf_361, w0_leaf_362]
#print axioms pw0_0360

theorem pw0_0361 : pw0 361 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 361 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather180, gather180]
  rw [hwe 180 (by omega), hwe 182 (by omega), hwo 180 (by omega), hwo 181 (by omega)]
  change -5*(w0 (2*180) - (half*w0 (2*180) + half*w0 (2*182))) + 7*w0 (2*180+1) + 5*(w0 (2*181+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_360, w0_leaf_361, w0_leaf_363, w0_leaf_364]
#print axioms pw0_0361

end
end AspisV8R19.R780Point02WeightChunk36P0
