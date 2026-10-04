import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk05
import AspisV8R19.R780Point02WeightSharedChunk06
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

namespace AspisV8R19.R780Point02WeightChunk29P0
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk05
open AspisV8R19.R780Point02WeightSharedChunk06
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

theorem pw0_0276 : pw0 276 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 276 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather138]
  rw [hwe 138 (by omega), hwe 139 (by omega), hwo 138 (by omega)]
  change 7*w0 (2*138) + 5*(w0 (2*139)) - 5*w0 (2*138+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_276, w0_leaf_277, w0_leaf_278]
#print axioms pw0_0276

theorem pw0_0277 : pw0 277 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 277 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather138, gather138]
  rw [hwe 136 (by omega), hwe 138 (by omega), hwe 140 (by omega), hwo 138 (by omega), hwo 139 (by omega)]
  change -5*(w0 (2*138) - (half*w0 (2*138) + half^2*w0 (2*136) + half^2*w0 (2*140))) + 7*w0 (2*138+1) + 5*(w0 (2*139+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_272, w0_leaf_276, w0_leaf_277, w0_leaf_279, w0_leaf_280]
#print axioms pw0_0277

theorem pw0_0279 : pw0 279 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 279 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather139, gather139]
  rw [hwe 137 (by omega), hwe 139 (by omega), hwe 141 (by omega), hwo 136 (by omega), hwo 138 (by omega), hwo 139 (by omega), hwo 140 (by omega)]
  change -5*(w0 (2*139) - (half*w0 (2*139) + half^2*w0 (2*137) + half^2*w0 (2*141))) + 7*w0 (2*139+1) + 5*(half^1*w0 (2*138+1) + half^2*w0 (2*136+1) + half^2*w0 (2*140+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0))
  rw [w0_leaf_273, w0_leaf_274, w0_leaf_277, w0_leaf_278, w0_leaf_279, w0_leaf_281, w0_leaf_282]
#print axioms pw0_0279

theorem pw0_0280 : pw0 280 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 280 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather140]
  rw [hwe 140 (by omega), hwe 141 (by omega), hwo 140 (by omega)]
  change 7*w0 (2*140) + 5*(w0 (2*141)) - 5*w0 (2*140+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_280, w0_leaf_281, w0_leaf_282]
#print axioms pw0_0280

theorem pw0_0281 : pw0 281 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 281 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather140, gather140]
  rw [hwe 140 (by omega), hwe 142 (by omega), hwo 140 (by omega), hwo 141 (by omega)]
  change -5*(w0 (2*140) - (half*w0 (2*140) + half*w0 (2*142))) + 7*w0 (2*140+1) + 5*(w0 (2*141+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_280, w0_leaf_281, w0_leaf_283, w0_leaf_284]
#print axioms pw0_0281

theorem pw0_0283 : pw0 283 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 283 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather141, gather141]
  rw [hwe 141 (by omega), hwe 143 (by omega), hwo 140 (by omega), hwo 141 (by omega), hwo 142 (by omega)]
  change -5*(w0 (2*141) - (half*w0 (2*141) + half*w0 (2*143))) + 7*w0 (2*141+1) + 5*(half^1*w0 (2*140+1) + half^1*w0 (2*142+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0))
  rw [w0_leaf_281, w0_leaf_282, w0_leaf_283, w0_leaf_285, w0_leaf_286]
#print axioms pw0_0283

theorem pw0_0284 : pw0 284 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 284 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather142]
  rw [hwe 142 (by omega), hwe 143 (by omega), hwo 142 (by omega)]
  change 7*w0 (2*142) + 5*(w0 (2*143)) - 5*w0 (2*142+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_284, w0_leaf_285, w0_leaf_286]
#print axioms pw0_0284

theorem pw0_0285 : pw0 285 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 285 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather142, gather142]
  rw [hwe 128 (by omega), hwe 136 (by omega), hwe 140 (by omega), hwe 142 (by omega), hwe 144 (by omega), hwo 142 (by omega), hwo 143 (by omega)]
  change -5*(w0 (2*142) - (half*w0 (2*142) + half^2*w0 (2*140) + half^3*w0 (2*136) + half^4*w0 (2*128) + half^4*w0 (2*144))) + 7*w0 (2*142+1) + 5*(w0 (2*143+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_256, w0_leaf_272, w0_leaf_280, w0_leaf_284, w0_leaf_285, w0_leaf_287, w0_leaf_288]
#print axioms pw0_0285

end
end AspisV8R19.R780Point02WeightChunk29P0
