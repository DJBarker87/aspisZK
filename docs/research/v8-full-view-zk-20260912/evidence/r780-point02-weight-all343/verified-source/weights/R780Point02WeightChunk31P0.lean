import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk06
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

namespace AspisV8R19.R780Point02WeightChunk31P0
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk06
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

theorem pw0_0297 : pw0 297 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 297 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather148, gather148]
  rw [hwe 148 (by omega), hwe 150 (by omega), hwo 148 (by omega), hwo 149 (by omega)]
  change -5*(w0 (2*148) - (half*w0 (2*148) + half*w0 (2*150))) + 7*w0 (2*148+1) + 5*(w0 (2*149+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_296, w0_leaf_297, w0_leaf_299, w0_leaf_300]
#print axioms pw0_0297

theorem pw0_0299 : pw0 299 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 299 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather149, gather149]
  rw [hwe 149 (by omega), hwe 151 (by omega), hwo 148 (by omega), hwo 149 (by omega), hwo 150 (by omega)]
  change -5*(w0 (2*149) - (half*w0 (2*149) + half*w0 (2*151))) + 7*w0 (2*149+1) + 5*(half^1*w0 (2*148+1) + half^1*w0 (2*150+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0))
  rw [w0_leaf_297, w0_leaf_298, w0_leaf_299, w0_leaf_301, w0_leaf_302]
#print axioms pw0_0299

theorem pw0_0300 : pw0 300 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 300 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather150]
  rw [hwe 150 (by omega), hwe 151 (by omega), hwo 150 (by omega)]
  change 7*w0 (2*150) + 5*(w0 (2*151)) - 5*w0 (2*150+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_300, w0_leaf_301, w0_leaf_302]
#print axioms pw0_0300

theorem pw0_0301 : pw0 301 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 301 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather150, gather150]
  rw [hwe 144 (by omega), hwe 148 (by omega), hwe 150 (by omega), hwe 152 (by omega), hwo 150 (by omega), hwo 151 (by omega)]
  change -5*(w0 (2*150) - (half*w0 (2*150) + half^2*w0 (2*148) + half^3*w0 (2*144) + half^3*w0 (2*152))) + 7*w0 (2*150+1) + 5*(w0 (2*151+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_288, w0_leaf_296, w0_leaf_300, w0_leaf_301, w0_leaf_303, w0_leaf_304]
#print axioms pw0_0301

theorem pw0_0303 : pw0 303 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^3*(0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 303 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather151, gather151]
  rw [hwe 145 (by omega), hwe 149 (by omega), hwe 151 (by omega), hwe 153 (by omega), hwo 144 (by omega), hwo 148 (by omega), hwo 150 (by omega), hwo 151 (by omega), hwo 152 (by omega)]
  change -5*(w0 (2*151) - (half*w0 (2*151) + half^2*w0 (2*149) + half^3*w0 (2*145) + half^3*w0 (2*153))) + 7*w0 (2*151+1) + 5*(half^1*w0 (2*150+1) + half^2*w0 (2*148+1) + half^3*w0 (2*144+1) + half^3*w0 (2*152+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^3*(0))
  rw [w0_leaf_289, w0_leaf_290, w0_leaf_297, w0_leaf_298, w0_leaf_301, w0_leaf_302, w0_leaf_303, w0_leaf_305, w0_leaf_306]
#print axioms pw0_0303

theorem pw0_0304 : pw0 304 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 304 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather152]
  rw [hwe 152 (by omega), hwe 153 (by omega), hwo 152 (by omega)]
  change 7*w0 (2*152) + 5*(w0 (2*153)) - 5*w0 (2*152+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_304, w0_leaf_305, w0_leaf_306]
#print axioms pw0_0304

theorem pw0_0305 : pw0 305 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 305 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather152, gather152]
  rw [hwe 152 (by omega), hwe 154 (by omega), hwo 152 (by omega), hwo 153 (by omega)]
  change -5*(w0 (2*152) - (half*w0 (2*152) + half*w0 (2*154))) + 7*w0 (2*152+1) + 5*(w0 (2*153+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_304, w0_leaf_305, w0_leaf_307, w0_leaf_308]
#print axioms pw0_0305

theorem pw0_0307 : pw0 307 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 307 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather153, gather153]
  rw [hwe 153 (by omega), hwe 155 (by omega), hwo 152 (by omega), hwo 153 (by omega), hwo 154 (by omega)]
  change -5*(w0 (2*153) - (half*w0 (2*153) + half*w0 (2*155))) + 7*w0 (2*153+1) + 5*(half^1*w0 (2*152+1) + half^1*w0 (2*154+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0))
  rw [w0_leaf_305, w0_leaf_306, w0_leaf_307, w0_leaf_309, w0_leaf_310]
#print axioms pw0_0307

end
end AspisV8R19.R780Point02WeightChunk31P0
