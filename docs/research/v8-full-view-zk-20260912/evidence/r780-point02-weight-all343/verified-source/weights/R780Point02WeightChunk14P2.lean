import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk02
import AspisV8R19.R780Point02WeightSharedChunk03
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

namespace AspisV8R19.R780Point02WeightChunk14P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk02
open AspisV8R19.R780Point02WeightSharedChunk03
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

theorem pw2_0169 : pw2 169 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 169 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather84, gather84]
  rw [hwe 84 (by omega), hwe 86 (by omega), hwo 84 (by omega), hwo 85 (by omega)]
  change -5*(w2 (2*84) - (half*w2 (2*84) + half*w2 (2*86))) + 7*w2 (2*84+1) + 5*(w2 (2*85+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_168, w2_leaf_169, w2_leaf_171, w2_leaf_172]
#print axioms pw2_0169

theorem pw2_0170 : pw2 170 = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 170 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather85]
  rw [hwe 84 (by omega), hwe 85 (by omega), hwe 86 (by omega), hwo 85 (by omega)]
  change 7*w2 (2*85) + 5*(half^1*w2 (2*84) + half^1*w2 (2*86)) - 5*w2 (2*85+1) = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0)
  rw [w2_leaf_168, w2_leaf_170, w2_leaf_171, w2_leaf_172]
#print axioms pw2_0170

theorem pw2_0172 : pw2 172 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 172 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather86]
  rw [hwe 86 (by omega), hwe 87 (by omega), hwo 86 (by omega)]
  change 7*w2 (2*86) + 5*(w2 (2*87)) - 5*w2 (2*86+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_172, w2_leaf_173, w2_leaf_174]
#print axioms pw2_0172

theorem pw2_0173 : pw2 173 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 173 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather86, gather86]
  rw [hwe 80 (by omega), hwe 84 (by omega), hwe 86 (by omega), hwe 88 (by omega), hwo 86 (by omega), hwo 87 (by omega)]
  change -5*(w2 (2*86) - (half*w2 (2*86) + half^2*w2 (2*84) + half^3*w2 (2*80) + half^3*w2 (2*88))) + 7*w2 (2*86+1) + 5*(w2 (2*87+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_160, w2_leaf_168, w2_leaf_172, w2_leaf_173, w2_leaf_175, w2_leaf_176]
#print axioms pw2_0173

end
end AspisV8R19.R780Point02WeightChunk14P2
