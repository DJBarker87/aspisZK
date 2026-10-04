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

namespace AspisV8R19.R780Point02WeightChunk30P2
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

theorem pw2_0287 : pw2 287 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 287 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather143, gather143]
  rw [hwe 129 (by omega), hwe 137 (by omega), hwe 141 (by omega), hwe 143 (by omega), hwe 145 (by omega), hwo 128 (by omega), hwo 136 (by omega), hwo 140 (by omega), hwo 142 (by omega), hwo 143 (by omega), hwo 144 (by omega)]
  change -5*(w2 (2*143) - (half*w2 (2*143) + half^2*w2 (2*141) + half^3*w2 (2*137) + half^4*w2 (2*129) + half^4*w2 (2*145))) + 7*w2 (2*143+1) + 5*(half^1*w2 (2*142+1) + half^2*w2 (2*140+1) + half^3*w2 (2*136+1) + half^4*w2 (2*128+1) + half^4*w2 (2*144+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(0))
  rw [w2_leaf_257, w2_leaf_258, w2_leaf_273, w2_leaf_274, w2_leaf_281, w2_leaf_282, w2_leaf_285, w2_leaf_286, w2_leaf_287, w2_leaf_289, w2_leaf_290]
#print axioms pw2_0287

theorem pw2_0288 : pw2 288 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 288 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather144]
  rw [hwe 144 (by omega), hwe 145 (by omega), hwo 144 (by omega)]
  change 7*w2 (2*144) + 5*(w2 (2*145)) - 5*w2 (2*144+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_288, w2_leaf_289, w2_leaf_290]
#print axioms pw2_0288

theorem pw2_0289 : pw2 289 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 289 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather144, gather144]
  rw [hwe 144 (by omega), hwe 146 (by omega), hwo 144 (by omega), hwo 145 (by omega)]
  change -5*(w2 (2*144) - (half*w2 (2*144) + half*w2 (2*146))) + 7*w2 (2*144+1) + 5*(w2 (2*145+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_288, w2_leaf_289, w2_leaf_291, w2_leaf_292]
#print axioms pw2_0289

theorem pw2_0291 : pw2 291 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 291 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather145, gather145]
  rw [hwe 145 (by omega), hwe 147 (by omega), hwo 144 (by omega), hwo 145 (by omega), hwo 146 (by omega)]
  change -5*(w2 (2*145) - (half*w2 (2*145) + half*w2 (2*147))) + 7*w2 (2*145+1) + 5*(half^1*w2 (2*144+1) + half^1*w2 (2*146+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0))
  rw [w2_leaf_289, w2_leaf_290, w2_leaf_291, w2_leaf_293, w2_leaf_294]
#print axioms pw2_0291

theorem pw2_0292 : pw2 292 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 292 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather146]
  rw [hwe 146 (by omega), hwe 147 (by omega), hwo 146 (by omega)]
  change 7*w2 (2*146) + 5*(w2 (2*147)) - 5*w2 (2*146+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_292, w2_leaf_293, w2_leaf_294]
#print axioms pw2_0292

theorem pw2_0293 : pw2 293 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 293 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather146, gather146]
  rw [hwe 144 (by omega), hwe 146 (by omega), hwe 148 (by omega), hwo 146 (by omega), hwo 147 (by omega)]
  change -5*(w2 (2*146) - (half*w2 (2*146) + half^2*w2 (2*144) + half^2*w2 (2*148))) + 7*w2 (2*146+1) + 5*(w2 (2*147+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_288, w2_leaf_292, w2_leaf_293, w2_leaf_295, w2_leaf_296]
#print axioms pw2_0293

theorem pw2_0295 : pw2 295 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 295 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather147, gather147]
  rw [hwe 145 (by omega), hwe 147 (by omega), hwe 149 (by omega), hwo 144 (by omega), hwo 146 (by omega), hwo 147 (by omega), hwo 148 (by omega)]
  change -5*(w2 (2*147) - (half*w2 (2*147) + half^2*w2 (2*145) + half^2*w2 (2*149))) + 7*w2 (2*147+1) + 5*(half^1*w2 (2*146+1) + half^2*w2 (2*144+1) + half^2*w2 (2*148+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0))
  rw [w2_leaf_289, w2_leaf_290, w2_leaf_293, w2_leaf_294, w2_leaf_295, w2_leaf_297, w2_leaf_298]
#print axioms pw2_0295

theorem pw2_0296 : pw2 296 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 296 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather148]
  rw [hwe 148 (by omega), hwe 149 (by omega), hwo 148 (by omega)]
  change 7*w2 (2*148) + 5*(w2 (2*149)) - 5*w2 (2*148+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_296, w2_leaf_297, w2_leaf_298]
#print axioms pw2_0296

end
end AspisV8R19.R780Point02WeightChunk30P2
