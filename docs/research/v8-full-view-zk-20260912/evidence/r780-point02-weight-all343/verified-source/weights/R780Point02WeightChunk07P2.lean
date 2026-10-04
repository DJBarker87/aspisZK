import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk01
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

namespace AspisV8R19.R780Point02WeightChunk07P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk01
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

theorem pw2_0132 : pw2 132 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 132 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather66]
  rw [hwe 66 (by omega), hwe 67 (by omega), hwo 66 (by omega)]
  change 7*w2 (2*66) + 5*(w2 (2*67)) - 5*w2 (2*66+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_132, w2_leaf_133, w2_leaf_134]
#print axioms pw2_0132

theorem pw2_0133 : pw2 133 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 133 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather66, gather66]
  rw [hwe 64 (by omega), hwe 66 (by omega), hwe 68 (by omega), hwo 66 (by omega), hwo 67 (by omega)]
  change -5*(w2 (2*66) - (half*w2 (2*66) + half^2*w2 (2*64) + half^2*w2 (2*68))) + 7*w2 (2*66+1) + 5*(w2 (2*67+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_128, w2_leaf_132, w2_leaf_133, w2_leaf_135, w2_leaf_136]
#print axioms pw2_0133

theorem pw2_0134 : pw2 134 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 134 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather67]
  rw [hwe 64 (by omega), hwe 66 (by omega), hwe 67 (by omega), hwe 68 (by omega), hwo 67 (by omega)]
  change 7*w2 (2*67) + 5*(half^1*w2 (2*66) + half^2*w2 (2*64) + half^2*w2 (2*68)) - 5*w2 (2*67+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0)
  rw [w2_leaf_128, w2_leaf_132, w2_leaf_134, w2_leaf_135, w2_leaf_136]
#print axioms pw2_0134

theorem pw2_0136 : pw2 136 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 136 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather68]
  rw [hwe 68 (by omega), hwe 69 (by omega), hwo 68 (by omega)]
  change 7*w2 (2*68) + 5*(w2 (2*69)) - 5*w2 (2*68+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_136, w2_leaf_137, w2_leaf_138]
#print axioms pw2_0136

end
end AspisV8R19.R780Point02WeightChunk07P2
