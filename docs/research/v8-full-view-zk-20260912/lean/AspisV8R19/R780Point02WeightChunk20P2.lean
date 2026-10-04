import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk03
import AspisV8R19.R780Point02WeightSharedChunk04
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

namespace AspisV8R19.R780Point02WeightChunk20P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk03
open AspisV8R19.R780Point02WeightSharedChunk04
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

theorem pw2_0205 : pw2 205 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 205 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather102, gather102]
  rw [hwe 96 (by omega), hwe 100 (by omega), hwe 102 (by omega), hwe 104 (by omega), hwo 102 (by omega), hwo 103 (by omega)]
  change -5*(w2 (2*102) - (half*w2 (2*102) + half^2*w2 (2*100) + half^3*w2 (2*96) + half^3*w2 (2*104))) + 7*w2 (2*102+1) + 5*(w2 (2*103+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_192, w2_leaf_200, w2_leaf_204, w2_leaf_205, w2_leaf_207, w2_leaf_208]
#print axioms pw2_0205

theorem pw2_0206 : pw2 206 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^3*(0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 206 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather103]
  rw [hwe 96 (by omega), hwe 100 (by omega), hwe 102 (by omega), hwe 103 (by omega), hwe 104 (by omega), hwo 103 (by omega)]
  change 7*w2 (2*103) + 5*(half^1*w2 (2*102) + half^2*w2 (2*100) + half^3*w2 (2*96) + half^3*w2 (2*104)) - 5*w2 (2*103+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^3*(0)) - 5*(0)
  rw [w2_leaf_192, w2_leaf_200, w2_leaf_204, w2_leaf_206, w2_leaf_207, w2_leaf_208]
#print axioms pw2_0206

theorem pw2_0208 : pw2 208 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 208 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather104]
  rw [hwe 104 (by omega), hwe 105 (by omega), hwo 104 (by omega)]
  change 7*w2 (2*104) + 5*(w2 (2*105)) - 5*w2 (2*104+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_208, w2_leaf_209, w2_leaf_210]
#print axioms pw2_0208

theorem pw2_0209 : pw2 209 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 209 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather104, gather104]
  rw [hwe 104 (by omega), hwe 106 (by omega), hwo 104 (by omega), hwo 105 (by omega)]
  change -5*(w2 (2*104) - (half*w2 (2*104) + half*w2 (2*106))) + 7*w2 (2*104+1) + 5*(w2 (2*105+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_208, w2_leaf_209, w2_leaf_211, w2_leaf_212]
#print axioms pw2_0209

end
end AspisV8R19.R780Point02WeightChunk20P2
