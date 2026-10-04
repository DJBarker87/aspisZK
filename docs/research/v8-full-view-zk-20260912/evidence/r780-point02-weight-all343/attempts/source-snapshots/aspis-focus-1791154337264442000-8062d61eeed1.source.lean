import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk05
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

namespace AspisV8R19.R780Point02WeightChunk32P0
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk05
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

theorem pw0_0308 : pw0 308 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 308 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather154]
  rw [hwe 154 (by omega), hwe 155 (by omega), hwo 154 (by omega)]
  change 7*w0 (2*154) + 5*(w0 (2*155)) - 5*w0 (2*154+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_308, w0_leaf_309, w0_leaf_310]
#print axioms pw0_0308

theorem pw0_0311 : pw0 311 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 311 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather155, gather155]
  rw [hwe 153 (by omega), hwe 155 (by omega), hwe 157 (by omega), hwo 152 (by omega), hwo 154 (by omega), hwo 155 (by omega), hwo 156 (by omega)]
  change -5*(w0 (2*155) - (half*w0 (2*155) + half^2*w0 (2*153) + half^2*w0 (2*157))) + 7*w0 (2*155+1) + 5*(half^1*w0 (2*154+1) + half^2*w0 (2*152+1) + half^2*w0 (2*156+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0))
  rw [w0_leaf_305, w0_leaf_306, w0_leaf_309, w0_leaf_310, w0_leaf_311, w0_leaf_313, w0_leaf_314]
#print axioms pw0_0311

theorem pw0_0312 : pw0 312 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 312 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather156]
  rw [hwe 156 (by omega), hwe 157 (by omega), hwo 156 (by omega)]
  change 7*w0 (2*156) + 5*(w0 (2*157)) - 5*w0 (2*156+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_312, w0_leaf_313, w0_leaf_314]
#print axioms pw0_0312

theorem pw0_0313 : pw0 313 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 313 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather156, gather156]
  rw [hwe 156 (by omega), hwe 158 (by omega), hwo 156 (by omega), hwo 157 (by omega)]
  change -5*(w0 (2*156) - (half*w0 (2*156) + half*w0 (2*158))) + 7*w0 (2*156+1) + 5*(w0 (2*157+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_312, w0_leaf_313, w0_leaf_315, w0_leaf_316]
#print axioms pw0_0313

theorem pw0_0315 : pw0 315 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 315 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather157, gather157]
  rw [hwe 157 (by omega), hwe 159 (by omega), hwo 156 (by omega), hwo 157 (by omega), hwo 158 (by omega)]
  change -5*(w0 (2*157) - (half*w0 (2*157) + half*w0 (2*159))) + 7*w0 (2*157+1) + 5*(half^1*w0 (2*156+1) + half^1*w0 (2*158+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*(half^1*(0) + half^1*(0))
  rw [w0_leaf_313, w0_leaf_314, w0_leaf_315, w0_leaf_317, w0_leaf_318]
#print axioms pw0_0315

theorem pw0_0316 : pw0 316 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 316 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather158]
  rw [hwe 158 (by omega), hwe 159 (by omega), hwo 158 (by omega)]
  change 7*w0 (2*158) + 5*(w0 (2*159)) - 5*w0 (2*158+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_316, w0_leaf_317, w0_leaf_318]
#print axioms pw0_0316

theorem pw0_0317 : pw0 317 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^5*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 317 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather158, gather158]
  rw [hwe 128 (by omega), hwe 144 (by omega), hwe 152 (by omega), hwe 156 (by omega), hwe 158 (by omega), hwe 160 (by omega), hwo 158 (by omega), hwo 159 (by omega)]
  change -5*(w0 (2*158) - (half*w0 (2*158) + half^2*w0 (2*156) + half^3*w0 (2*152) + half^4*w0 (2*144) + half^5*w0 (2*128) + half^5*w0 (2*160))) + 7*w0 (2*158+1) + 5*(w0 (2*159+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^5*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_256, w0_leaf_288, w0_leaf_304, w0_leaf_312, w0_leaf_316, w0_leaf_317, w0_leaf_319, w0_leaf_320]
#print axioms pw0_0317

theorem pw0_0319 : pw0 319 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^5*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^5*(0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 319 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather159, gather159]
  rw [hwe 129 (by omega), hwe 145 (by omega), hwe 153 (by omega), hwe 157 (by omega), hwe 159 (by omega), hwe 161 (by omega), hwo 128 (by omega), hwo 144 (by omega), hwo 152 (by omega), hwo 156 (by omega), hwo 158 (by omega), hwo 159 (by omega), hwo 160 (by omega)]
  change -5*(w0 (2*159) - (half*w0 (2*159) + half^2*w0 (2*157) + half^3*w0 (2*153) + half^4*w0 (2*145) + half^5*w0 (2*129) + half^5*w0 (2*161))) + 7*w0 (2*159+1) + 5*(half^1*w0 (2*158+1) + half^2*w0 (2*156+1) + half^3*w0 (2*152+1) + half^4*w0 (2*144+1) + half^5*w0 (2*128+1) + half^5*w0 (2*160+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^5*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^5*(0))
  rw [w0_leaf_257, w0_leaf_258, w0_leaf_289, w0_leaf_290, w0_leaf_305, w0_leaf_306, w0_leaf_313, w0_leaf_314, w0_leaf_317, w0_leaf_318, w0_leaf_319, w0_leaf_321, w0_leaf_322]
#print axioms pw0_0319

end
end AspisV8R19.R780Point02WeightChunk32P0
