import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk07
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

namespace AspisV8R19.R780Point02WeightChunk35P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk07
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

theorem pw2_0341 : pw2 341 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 341 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather170, gather170]
  rw [hwe 168 (by omega), hwe 170 (by omega), hwe 172 (by omega), hwo 170 (by omega), hwo 171 (by omega)]
  change -5*(w2 (2*170) - (half*w2 (2*170) + half^2*w2 (2*168) + half^2*w2 (2*172))) + 7*w2 (2*170+1) + 5*(w2 (2*171+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_336, w2_leaf_340, w2_leaf_341, w2_leaf_343, w2_leaf_344]
#print axioms pw2_0341

theorem pw2_0343 : pw2 343 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 343 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather171, gather171]
  rw [hwe 169 (by omega), hwe 171 (by omega), hwe 173 (by omega), hwo 168 (by omega), hwo 170 (by omega), hwo 171 (by omega), hwo 172 (by omega)]
  change -5*(w2 (2*171) - (half*w2 (2*171) + half^2*w2 (2*169) + half^2*w2 (2*173))) + 7*w2 (2*171+1) + 5*(half^1*w2 (2*170+1) + half^2*w2 (2*168+1) + half^2*w2 (2*172+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0))
  rw [w2_leaf_337, w2_leaf_338, w2_leaf_341, w2_leaf_342, w2_leaf_343, w2_leaf_345, w2_leaf_346]
#print axioms pw2_0343

theorem pw2_0344 : pw2 344 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 344 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather172]
  rw [hwe 172 (by omega), hwe 173 (by omega), hwo 172 (by omega)]
  change 7*w2 (2*172) + 5*(w2 (2*173)) - 5*w2 (2*172+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_344, w2_leaf_345, w2_leaf_346]
#print axioms pw2_0344

theorem pw2_0345 : pw2 345 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 345 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather172, gather172]
  rw [hwe 172 (by omega), hwe 174 (by omega), hwo 172 (by omega), hwo 173 (by omega)]
  change -5*(w2 (2*172) - (half*w2 (2*172) + half*w2 (2*174))) + 7*w2 (2*172+1) + 5*(w2 (2*173+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_344, w2_leaf_345, w2_leaf_347, w2_leaf_348]
#print axioms pw2_0345

theorem pw2_0347 : pw2 347 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 347 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather173, gather173]
  rw [hwe 173 (by omega), hwe 175 (by omega), hwo 172 (by omega), hwo 173 (by omega), hwo 174 (by omega)]
  change -5*(w2 (2*173) - (half*w2 (2*173) + half*w2 (2*175))) + 7*w2 (2*173+1) + 5*(half^1*w2 (2*172+1) + half^1*w2 (2*174+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0))
  rw [w2_leaf_345, w2_leaf_346, w2_leaf_347, w2_leaf_349, w2_leaf_350]
#print axioms pw2_0347

theorem pw2_0348 : pw2 348 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 348 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather174]
  rw [hwe 174 (by omega), hwe 175 (by omega), hwo 174 (by omega)]
  change 7*w2 (2*174) + 5*(w2 (2*175)) - 5*w2 (2*174+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_348, w2_leaf_349, w2_leaf_350]
#print axioms pw2_0348

theorem pw2_0349 : pw2 349 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 349 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather174, gather174]
  rw [hwe 160 (by omega), hwe 168 (by omega), hwe 172 (by omega), hwe 174 (by omega), hwe 176 (by omega), hwo 174 (by omega), hwo 175 (by omega)]
  change -5*(w2 (2*174) - (half*w2 (2*174) + half^2*w2 (2*172) + half^3*w2 (2*168) + half^4*w2 (2*160) + half^4*w2 (2*176))) + 7*w2 (2*174+1) + 5*(w2 (2*175+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_320, w2_leaf_336, w2_leaf_344, w2_leaf_348, w2_leaf_349, w2_leaf_351, w2_leaf_352]
#print axioms pw2_0349

theorem pw2_0351 : pw2 351 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 351 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather175, gather175]
  rw [hwe 161 (by omega), hwe 169 (by omega), hwe 173 (by omega), hwe 175 (by omega), hwe 177 (by omega), hwo 160 (by omega), hwo 168 (by omega), hwo 172 (by omega), hwo 174 (by omega), hwo 175 (by omega), hwo 176 (by omega)]
  change -5*(w2 (2*175) - (half*w2 (2*175) + half^2*w2 (2*173) + half^3*w2 (2*169) + half^4*w2 (2*161) + half^4*w2 (2*177))) + 7*w2 (2*175+1) + 5*(half^1*w2 (2*174+1) + half^2*w2 (2*172+1) + half^3*w2 (2*168+1) + half^4*w2 (2*160+1) + half^4*w2 (2*176+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(0))
  rw [w2_leaf_321, w2_leaf_322, w2_leaf_337, w2_leaf_338, w2_leaf_345, w2_leaf_346, w2_leaf_349, w2_leaf_350, w2_leaf_351, w2_leaf_353, w2_leaf_354]
#print axioms pw2_0351

end
end AspisV8R19.R780Point02WeightChunk35P2
