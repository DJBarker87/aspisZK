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

namespace AspisV8R19.R780Point02WeightChunk23P0
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

theorem pw0_0221 : pw0 221 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 221 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather110, gather110]
  rw [hwe 96 (by omega), hwe 104 (by omega), hwe 108 (by omega), hwe 110 (by omega), hwe 112 (by omega), hwo 110 (by omega), hwo 111 (by omega)]
  change -5*(w0 (2*110) - (half*w0 (2*110) + half^2*w0 (2*108) + half^3*w0 (2*104) + half^4*w0 (2*96) + half^4*w0 (2*112))) + 7*w0 (2*110+1) + 5*(w0 (2*111+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod))) + 7*(0) + 5*((0))
  rw [w0_leaf_192, w0_leaf_208, w0_leaf_216, w0_leaf_220, w0_leaf_221, w0_leaf_223, w0_leaf_224]
#print axioms pw0_0221

theorem pw0_0222 : pw0 222 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 222 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather111]
  rw [hwe 96 (by omega), hwe 104 (by omega), hwe 108 (by omega), hwe 110 (by omega), hwe 111 (by omega), hwe 112 (by omega), hwo 111 (by omega)]
  change 7*w0 (2*111) + 5*(half^1*w0 (2*110) + half^2*w0 (2*108) + half^3*w0 (2*104) + half^4*w0 (2*96) + half^4*w0 (2*112)) - 5*w0 (2*111+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod)) - 5*(0)
  rw [w0_leaf_192, w0_leaf_208, w0_leaf_216, w0_leaf_220, w0_leaf_222, w0_leaf_223, w0_leaf_224]
#print axioms pw0_0222

theorem pw0_0224 : pw0 224 = 7*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, -1, -2, -3, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, -2, -3, -1, 2, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w0 7 5 (-5) 224 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather112]
  rw [hwe 112 (by omega), hwe 113 (by omega), hwo 112 (by omega)]
  change 7*w0 (2*112) + 5*(w0 (2*113)) - 5*w0 (2*112+1) = 7*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, -1, -2, -3, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, -2, -3, -1, 2, 3, 1, 2] : List M).prod)
  rw [w0_leaf_224, w0_leaf_225, w0_leaf_226]
#print axioms pw0_0224

theorem pw0_0225 : pw0 225 = -5*((([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half*(([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, -1, -2, -3, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, -1, -2, -3, 2, 2, 3, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w0 7 5 (-5) 225 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather112, gather112]
  rw [hwe 112 (by omega), hwe 114 (by omega), hwo 112 (by omega), hwo 113 (by omega)]
  change -5*(w0 (2*112) - (half*w0 (2*112) + half*w0 (2*114))) + 7*w0 (2*112+1) + 5*(w0 (2*113+1)) = -5*((([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half*(([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, -1, -2, -3, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, -1, -2, -3, 2, 2, 3, 1, 2] : List M).prod))
  rw [w0_leaf_224, w0_leaf_225, w0_leaf_227, w0_leaf_228]
#print axioms pw0_0225

end
end AspisV8R19.R780Point02WeightChunk23P0
