import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk16
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

namespace AspisV8R19.R780Point02WeightChunk55P0
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk16
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

theorem pw0_1017 : pw0 1017 = -5*((([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w0 7 5 (-5) 1017 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather508, gather508]
  rw [hwe 508 (by omega), hwe 510 (by omega), hwo 508 (by omega), hwo 509 (by omega)]
  change -5*(w0 (2*508) - (half*w0 (2*508) + half*w0 (2*510))) + 7*w0 (2*508+1) + 5*(w0 (2*509+1)) = -5*((([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List M).prod))
  rw [w0_leaf_1016, w0_leaf_1017, w0_leaf_1019, w0_leaf_1020]
#print axioms pw0_1017

theorem pw0_1018 : pw0 1018 = 7*(([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + half^1*(([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w0 7 5 (-5) 1018 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather509]
  rw [hwe 508 (by omega), hwe 509 (by omega), hwe 510 (by omega), hwo 509 (by omega)]
  change 7*w0 (2*509) + 5*(half^1*w0 (2*508) + half^1*w0 (2*510)) - 5*w0 (2*509+1) = 7*(([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod) + half^1*(([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List M).prod)
  rw [w0_leaf_1016, w0_leaf_1018, w0_leaf_1019, w0_leaf_1020]
#print axioms pw0_1018

theorem pw0_1019 : pw0 1019 = -5*((([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, 3, 4, 2, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List M).prod) + half^1*(0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 1019 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather509, gather509]
  rw [hwe 509 (by omega), hwe 511 (by omega), hwo 508 (by omega), hwo 509 (by omega), hwo 510 (by omega)]
  change -5*(w0 (2*509) - (half*w0 (2*509) + half*w0 (2*511))) + 7*w0 (2*509+1) + 5*(half^1*w0 (2*508+1) + half^1*w0 (2*510+1)) = -5*((([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, 3, 4, 2, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List M).prod) + half^1*(0))
  rw [w0_leaf_1017, w0_leaf_1018, w0_leaf_1019, w0_leaf_1021, w0_leaf_1022]
#print axioms pw0_1019

end
end AspisV8R19.R780Point02WeightChunk55P0
