import AspisV8R19.R780Point02WeightShared
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

namespace AspisV8R19.R780Point02WeightChunk18P0
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
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

theorem pw0_0194 : pw0 194 = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 194 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather97]
  rw [hwe 96 (by omega), hwe 97 (by omega), hwe 98 (by omega), hwo 97 (by omega)]
  change 7*w0 (2*97) + 5*(half^1*w0 (2*96) + half^1*w0 (2*98)) - 5*w0 (2*97+1) = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0)
  rw [w0_leaf_192, w0_leaf_194, w0_leaf_195, w0_leaf_196]
#print axioms pw0_0194

theorem pw0_0196 : pw0 196 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 196 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather98]
  rw [hwe 98 (by omega), hwe 99 (by omega), hwo 98 (by omega)]
  change 7*w0 (2*98) + 5*(w0 (2*99)) - 5*w0 (2*98+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_196, w0_leaf_197, w0_leaf_198]
#print axioms pw0_0196

theorem pw0_0197 : pw0 197 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 197 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather98, gather98]
  rw [hwe 96 (by omega), hwe 98 (by omega), hwe 100 (by omega), hwo 98 (by omega), hwo 99 (by omega)]
  change -5*(w0 (2*98) - (half*w0 (2*98) + half^2*w0 (2*96) + half^2*w0 (2*100))) + 7*w0 (2*98+1) + 5*(w0 (2*99+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_192, w0_leaf_196, w0_leaf_197, w0_leaf_199, w0_leaf_200]
#print axioms pw0_0197

theorem pw0_0198 : pw0 198 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 198 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather99]
  rw [hwe 96 (by omega), hwe 98 (by omega), hwe 99 (by omega), hwe 100 (by omega), hwo 99 (by omega)]
  change 7*w0 (2*99) + 5*(half^1*w0 (2*98) + half^2*w0 (2*96) + half^2*w0 (2*100)) - 5*w0 (2*99+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0)
  rw [w0_leaf_192, w0_leaf_196, w0_leaf_198, w0_leaf_199, w0_leaf_200]
#print axioms pw0_0198

end
end AspisV8R19.R780Point02WeightChunk18P0
