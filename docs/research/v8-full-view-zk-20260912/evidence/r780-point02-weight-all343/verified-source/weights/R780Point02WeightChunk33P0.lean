import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk07
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

namespace AspisV8R19.R780Point02WeightChunk33P0
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk07
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

theorem pw0_0320 : pw0 320 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 320 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather160]
  rw [hwe 160 (by omega), hwe 161 (by omega), hwo 160 (by omega)]
  change 7*w0 (2*160) + 5*(w0 (2*161)) - 5*w0 (2*160+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_320, w0_leaf_321, w0_leaf_322]
#print axioms pw0_0320

theorem pw0_0321 : pw0 321 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 321 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather160, gather160]
  rw [hwe 160 (by omega), hwe 162 (by omega), hwo 160 (by omega), hwo 161 (by omega)]
  change -5*(w0 (2*160) - (half*w0 (2*160) + half*w0 (2*162))) + 7*w0 (2*160+1) + 5*(w0 (2*161+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_320, w0_leaf_321, w0_leaf_323, w0_leaf_324]
#print axioms pw0_0321

theorem pw0_0323 : pw0 323 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 323 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather161, gather161]
  rw [hwe 161 (by omega), hwe 163 (by omega), hwo 160 (by omega), hwo 161 (by omega), hwo 162 (by omega)]
  change -5*(w0 (2*161) - (half*w0 (2*161) + half*w0 (2*163))) + 7*w0 (2*161+1) + 5*(half^1*w0 (2*160+1) + half^1*w0 (2*162+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0))
  rw [w0_leaf_321, w0_leaf_322, w0_leaf_323, w0_leaf_325, w0_leaf_326]
#print axioms pw0_0323

theorem pw0_0324 : pw0 324 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 324 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather162]
  rw [hwe 162 (by omega), hwe 163 (by omega), hwo 162 (by omega)]
  change 7*w0 (2*162) + 5*(w0 (2*163)) - 5*w0 (2*162+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_324, w0_leaf_325, w0_leaf_326]
#print axioms pw0_0324

theorem pw0_0325 : pw0 325 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 325 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather162, gather162]
  rw [hwe 160 (by omega), hwe 162 (by omega), hwe 164 (by omega), hwo 162 (by omega), hwo 163 (by omega)]
  change -5*(w0 (2*162) - (half*w0 (2*162) + half^2*w0 (2*160) + half^2*w0 (2*164))) + 7*w0 (2*162+1) + 5*(w0 (2*163+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_320, w0_leaf_324, w0_leaf_325, w0_leaf_327, w0_leaf_328]
#print axioms pw0_0325

theorem pw0_0327 : pw0 327 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 327 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather163, gather163]
  rw [hwe 161 (by omega), hwe 163 (by omega), hwe 165 (by omega), hwo 160 (by omega), hwo 162 (by omega), hwo 163 (by omega), hwo 164 (by omega)]
  change -5*(w0 (2*163) - (half*w0 (2*163) + half^2*w0 (2*161) + half^2*w0 (2*165))) + 7*w0 (2*163+1) + 5*(half^1*w0 (2*162+1) + half^2*w0 (2*160+1) + half^2*w0 (2*164+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0))
  rw [w0_leaf_321, w0_leaf_322, w0_leaf_325, w0_leaf_326, w0_leaf_327, w0_leaf_329, w0_leaf_330]
#print axioms pw0_0327

theorem pw0_0328 : pw0 328 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 328 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather164]
  rw [hwe 164 (by omega), hwe 165 (by omega), hwo 164 (by omega)]
  change 7*w0 (2*164) + 5*(w0 (2*165)) - 5*w0 (2*164+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_328, w0_leaf_329, w0_leaf_330]
#print axioms pw0_0328

theorem pw0_0329 : pw0 329 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 329 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather164, gather164]
  rw [hwe 164 (by omega), hwe 166 (by omega), hwo 164 (by omega), hwo 165 (by omega)]
  change -5*(w0 (2*164) - (half*w0 (2*164) + half*w0 (2*166))) + 7*w0 (2*164+1) + 5*(w0 (2*165+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_328, w0_leaf_329, w0_leaf_331, w0_leaf_332]
#print axioms pw0_0329

end
end AspisV8R19.R780Point02WeightChunk33P0
