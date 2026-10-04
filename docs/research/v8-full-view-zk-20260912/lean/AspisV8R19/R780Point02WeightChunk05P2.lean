import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk00
import AspisV8R19.R780Point02WeightSharedChunk01
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

namespace AspisV8R19.R780Point02WeightChunk05P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk00
open AspisV8R19.R780Point02WeightSharedChunk01
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

theorem pw2_0121 : pw2 121 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 121 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather60, gather60]
  rw [hwe 60 (by omega), hwe 62 (by omega), hwo 60 (by omega), hwo 61 (by omega)]
  change -5*(w2 (2*60) - (half*w2 (2*60) + half*w2 (2*62))) + 7*w2 (2*60+1) + 5*(w2 (2*61+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_120, w2_leaf_121, w2_leaf_123, w2_leaf_124]
#print axioms pw2_0121

theorem pw2_0122 : pw2 122 = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 122 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather61]
  rw [hwe 60 (by omega), hwe 61 (by omega), hwe 62 (by omega), hwo 61 (by omega)]
  change 7*w2 (2*61) + 5*(half^1*w2 (2*60) + half^1*w2 (2*62)) - 5*w2 (2*61+1) = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0)
  rw [w2_leaf_120, w2_leaf_122, w2_leaf_123, w2_leaf_124]
#print axioms pw2_0122

theorem pw2_0124 : pw2 124 = 7*(0) + 5*((([1, 1, 2, 3, 4, -1, 2, 3, 1, 2] : List M).prod)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 124 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather62]
  rw [hwe 62 (by omega), hwe 63 (by omega), hwo 62 (by omega)]
  change 7*w2 (2*62) + 5*(w2 (2*63)) - 5*w2 (2*62+1) = 7*(0) + 5*((([1, 1, 2, 3, 4, -1, 2, 3, 1, 2] : List M).prod)) - 5*(0)
  rw [w2_leaf_124, w2_leaf_125, w2_leaf_126]
#print axioms pw2_0124

theorem pw2_0125 : pw2 125 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^6*(0) + half^6*(0))) + 7*(0) + 5*((([1, 1, 2, 3, 4, 2, 2, 3, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 125 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather62, gather62]
  rw [hwe 0 (by omega), hwe 32 (by omega), hwe 48 (by omega), hwe 56 (by omega), hwe 60 (by omega), hwe 62 (by omega), hwe 64 (by omega), hwo 62 (by omega), hwo 63 (by omega)]
  change -5*(w2 (2*62) - (half*w2 (2*62) + half^2*w2 (2*60) + half^3*w2 (2*56) + half^4*w2 (2*48) + half^5*w2 (2*32) + half^6*w2 (2*0) + half^6*w2 (2*64))) + 7*w2 (2*62+1) + 5*(w2 (2*63+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^6*(0) + half^6*(0))) + 7*(0) + 5*((([1, 1, 2, 3, 4, 2, 2, 3, 1, 2] : List M).prod))
  rw [w2_leaf_0, w2_leaf_64, w2_leaf_96, w2_leaf_112, w2_leaf_120, w2_leaf_124, w2_leaf_125, w2_leaf_127, w2_leaf_128]
#print axioms pw2_0125

end
end AspisV8R19.R780Point02WeightChunk05P2
