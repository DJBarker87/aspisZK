import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk15
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

namespace AspisV8R19.R780Point02WeightChunk54P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk15
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

theorem pw2_1006 : pw2 1006 = 7*(([1, 1, -1, 3, 4, 2, 2, 3, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + half^3*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, 4, 2, 2, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 1006 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather503]
  rw [hwe 496 (by omega), hwe 500 (by omega), hwe 502 (by omega), hwe 503 (by omega), hwe 504 (by omega), hwo 503 (by omega)]
  change 7*w2 (2*503) + 5*(half^1*w2 (2*502) + half^2*w2 (2*500) + half^3*w2 (2*496) + half^3*w2 (2*504)) - 5*w2 (2*503+1) = 7*(([1, 1, -1, 3, 4, 2, 2, 3, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + half^3*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, 4, 2, 2, 3, 1, 2] : List M).prod)
  rw [w2_leaf_992, w2_leaf_1000, w2_leaf_1004, w2_leaf_1006, w2_leaf_1007, w2_leaf_1008]
#print axioms pw2_1006

theorem pw2_1008 : pw2 1008 = 7*(([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 1008 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather504]
  rw [hwe 504 (by omega), hwe 505 (by omega), hwo 504 (by omega)]
  change 7*w2 (2*504) + 5*(w2 (2*505)) - 5*w2 (2*504+1) = 7*(([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List M).prod)
  rw [w2_leaf_1008, w2_leaf_1009, w2_leaf_1010]
#print axioms pw2_1008

theorem pw2_1009 : pw2 1009 = -5*((([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half*(([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, 2, -2, -3, 2, 2, 3, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 1009 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather504, gather504]
  rw [hwe 504 (by omega), hwe 506 (by omega), hwo 504 (by omega), hwo 505 (by omega)]
  change -5*(w2 (2*504) - (half*w2 (2*504) + half*w2 (2*506))) + 7*w2 (2*504+1) + 5*(w2 (2*505+1)) = -5*((([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half*(([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, 2, -2, -3, 2, 2, 3, 1, 2] : List M).prod))
  rw [w2_leaf_1008, w2_leaf_1009, w2_leaf_1011, w2_leaf_1012]
#print axioms pw2_1009

theorem pw2_1011 : pw2 1011 = -5*((([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List M).prod) + half*(([1, 1, 2, -2, 4, 2, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, -3, 2, 2, 3, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List M).prod) + half^1*(([1, 1, 2, -2, 4, -1, 2, 3, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 1011 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather505, gather505]
  rw [hwe 505 (by omega), hwe 507 (by omega), hwo 504 (by omega), hwo 505 (by omega), hwo 506 (by omega)]
  change -5*(w2 (2*505) - (half*w2 (2*505) + half*w2 (2*507))) + 7*w2 (2*505+1) + 5*(half^1*w2 (2*504+1) + half^1*w2 (2*506+1)) = -5*((([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List M).prod) + half*(([1, 1, 2, -2, 4, 2, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, -3, 2, 2, 3, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List M).prod) + half^1*(([1, 1, 2, -2, 4, -1, 2, 3, 1, 2] : List M).prod))
  rw [w2_leaf_1009, w2_leaf_1010, w2_leaf_1011, w2_leaf_1013, w2_leaf_1014]
#print axioms pw2_1011

theorem pw2_1012 : pw2 1012 = 7*(([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, 2, -2, 4, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, 2, -2, 4, -1, 2, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 1012 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather506]
  rw [hwe 506 (by omega), hwe 507 (by omega), hwo 506 (by omega)]
  change 7*w2 (2*506) + 5*(w2 (2*507)) - 5*w2 (2*506+1) = 7*(([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, 2, -2, 4, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, 2, -2, 4, -1, 2, 3, 1, 2] : List M).prod)
  rw [w2_leaf_1012, w2_leaf_1013, w2_leaf_1014]
#print axioms pw2_1012

theorem pw2_1013 : pw2 1013 = -5*((([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, 4, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, 2, -2, 4, 2, 2, 3, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 1013 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather506, gather506]
  rw [hwe 504 (by omega), hwe 506 (by omega), hwe 508 (by omega), hwo 506 (by omega), hwo 507 (by omega)]
  change -5*(w2 (2*506) - (half*w2 (2*506) + half^2*w2 (2*504) + half^2*w2 (2*508))) + 7*w2 (2*506+1) + 5*(w2 (2*507+1)) = -5*((([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, 4, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, 2, -2, 4, 2, 2, 3, 1, 2] : List M).prod))
  rw [w2_leaf_1008, w2_leaf_1012, w2_leaf_1013, w2_leaf_1015, w2_leaf_1016]
#print axioms pw2_1013

theorem pw2_1015 : pw2 1015 = -5*((([1, 1, 2, -2, 4, 2, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, 4, 2, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, 2, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, 4, 2, 2, 3, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, -2, 4, -1, 2, 3, 1, 2] : List M).prod) + half^2*(([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, 2, 3, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 1015 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather507, gather507]
  rw [hwe 505 (by omega), hwe 507 (by omega), hwe 509 (by omega), hwo 504 (by omega), hwo 506 (by omega), hwo 507 (by omega), hwo 508 (by omega)]
  change -5*(w2 (2*507) - (half*w2 (2*507) + half^2*w2 (2*505) + half^2*w2 (2*509))) + 7*w2 (2*507+1) + 5*(half^1*w2 (2*506+1) + half^2*w2 (2*504+1) + half^2*w2 (2*508+1)) = -5*((([1, 1, 2, -2, 4, 2, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, 4, 2, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, 2, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, 4, 2, 2, 3, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, -2, 4, -1, 2, 3, 1, 2] : List M).prod) + half^2*(([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, 2, 3, 1, 2] : List M).prod))
  rw [w2_leaf_1009, w2_leaf_1010, w2_leaf_1013, w2_leaf_1014, w2_leaf_1015, w2_leaf_1017, w2_leaf_1018]
#print axioms pw2_1015

theorem pw2_1016 : pw2 1016 = 7*(([1, 1, 2, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, 2, 3, -3, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, 2, 3, -3, -1, 2, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 1016 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather508]
  rw [hwe 508 (by omega), hwe 509 (by omega), hwo 508 (by omega)]
  change 7*w2 (2*508) + 5*(w2 (2*509)) - 5*w2 (2*508+1) = 7*(([1, 1, 2, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, 2, 3, -3, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, 2, 3, -3, -1, 2, 3, 1, 2] : List M).prod)
  rw [w2_leaf_1016, w2_leaf_1017, w2_leaf_1018]
#print axioms pw2_1016

end
end AspisV8R19.R780Point02WeightChunk54P2
