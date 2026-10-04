import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk02
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

namespace AspisV8R19.R780Point02WeightChunk13P0
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk02
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

theorem pw0_0164 : pw0 164 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 164 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather82]
  rw [hwe 82 (by omega), hwe 83 (by omega), hwo 82 (by omega)]
  change 7*w0 (2*82) + 5*(w0 (2*83)) - 5*w0 (2*82+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_164, w0_leaf_165, w0_leaf_166]
#print axioms pw0_0164

theorem pw0_0165 : pw0 165 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 165 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather82, gather82]
  rw [hwe 80 (by omega), hwe 82 (by omega), hwe 84 (by omega), hwo 82 (by omega), hwo 83 (by omega)]
  change -5*(w0 (2*82) - (half*w0 (2*82) + half^2*w0 (2*80) + half^2*w0 (2*84))) + 7*w0 (2*82+1) + 5*(w0 (2*83+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_160, w0_leaf_164, w0_leaf_165, w0_leaf_167, w0_leaf_168]
#print axioms pw0_0165

theorem pw0_0166 : pw0 166 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 166 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather83]
  rw [hwe 80 (by omega), hwe 82 (by omega), hwe 83 (by omega), hwe 84 (by omega), hwo 83 (by omega)]
  change 7*w0 (2*83) + 5*(half^1*w0 (2*82) + half^2*w0 (2*80) + half^2*w0 (2*84)) - 5*w0 (2*83+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0)
  rw [w0_leaf_160, w0_leaf_164, w0_leaf_166, w0_leaf_167, w0_leaf_168]
#print axioms pw0_0166

theorem pw0_0168 : pw0 168 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 168 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather84]
  rw [hwe 84 (by omega), hwe 85 (by omega), hwo 84 (by omega)]
  change 7*w0 (2*84) + 5*(w0 (2*85)) - 5*w0 (2*84+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_168, w0_leaf_169, w0_leaf_170]
#print axioms pw0_0168

end
end AspisV8R19.R780Point02WeightChunk13P0
