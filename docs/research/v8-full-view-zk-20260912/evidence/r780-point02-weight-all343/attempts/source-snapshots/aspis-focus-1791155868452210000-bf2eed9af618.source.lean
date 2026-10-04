import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk14
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

namespace AspisV8R19.R780Point02WeightChunk50P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk14
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

theorem pw2_0964 : pw2 964 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 964 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather482]
  rw [hwe 482 (by omega), hwe 483 (by omega), hwo 482 (by omega)]
  change 7*w2 (2*482) + 5*(w2 (2*483)) - 5*w2 (2*482+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_964, w2_leaf_965, w2_leaf_966]
#print axioms pw2_0964

theorem pw2_0965 : pw2 965 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 965 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather482, gather482]
  rw [hwe 480 (by omega), hwe 482 (by omega), hwe 484 (by omega), hwo 482 (by omega), hwo 483 (by omega)]
  change -5*(w2 (2*482) - (half*w2 (2*482) + half^2*w2 (2*480) + half^2*w2 (2*484))) + 7*w2 (2*482+1) + 5*(w2 (2*483+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_960, w2_leaf_964, w2_leaf_965, w2_leaf_967, w2_leaf_968]
#print axioms pw2_0965

theorem pw2_0966 : pw2 966 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 966 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather483]
  rw [hwe 480 (by omega), hwe 482 (by omega), hwe 483 (by omega), hwe 484 (by omega), hwo 483 (by omega)]
  change 7*w2 (2*483) + 5*(half^1*w2 (2*482) + half^2*w2 (2*480) + half^2*w2 (2*484)) - 5*w2 (2*483+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0)
  rw [w2_leaf_960, w2_leaf_964, w2_leaf_966, w2_leaf_967, w2_leaf_968]
#print axioms pw2_0966

theorem pw2_0968 : pw2 968 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 968 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather484]
  rw [hwe 484 (by omega), hwe 485 (by omega), hwo 484 (by omega)]
  change 7*w2 (2*484) + 5*(w2 (2*485)) - 5*w2 (2*484+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_968, w2_leaf_969, w2_leaf_970]
#print axioms pw2_0968

theorem pw2_0969 : pw2 969 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 969 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather484, gather484]
  rw [hwe 484 (by omega), hwe 486 (by omega), hwo 484 (by omega), hwo 485 (by omega)]
  change -5*(w2 (2*484) - (half*w2 (2*484) + half*w2 (2*486))) + 7*w2 (2*484+1) + 5*(w2 (2*485+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_968, w2_leaf_969, w2_leaf_971, w2_leaf_972]
#print axioms pw2_0969

theorem pw2_0970 : pw2 970 = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 970 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather485]
  rw [hwe 484 (by omega), hwe 485 (by omega), hwe 486 (by omega), hwo 485 (by omega)]
  change 7*w2 (2*485) + 5*(half^1*w2 (2*484) + half^1*w2 (2*486)) - 5*w2 (2*485+1) = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0)
  rw [w2_leaf_968, w2_leaf_970, w2_leaf_971, w2_leaf_972]
#print axioms pw2_0970

theorem pw2_0972 : pw2 972 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 972 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather486]
  rw [hwe 486 (by omega), hwe 487 (by omega), hwo 486 (by omega)]
  change 7*w2 (2*486) + 5*(w2 (2*487)) - 5*w2 (2*486+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_972, w2_leaf_973, w2_leaf_974]
#print axioms pw2_0972

theorem pw2_0973 : pw2 973 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 973 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather486, gather486]
  rw [hwe 480 (by omega), hwe 484 (by omega), hwe 486 (by omega), hwe 488 (by omega), hwo 486 (by omega), hwo 487 (by omega)]
  change -5*(w2 (2*486) - (half*w2 (2*486) + half^2*w2 (2*484) + half^3*w2 (2*480) + half^3*w2 (2*488))) + 7*w2 (2*486+1) + 5*(w2 (2*487+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_960, w2_leaf_968, w2_leaf_972, w2_leaf_973, w2_leaf_975, w2_leaf_976]
#print axioms pw2_0973

end
end AspisV8R19.R780Point02WeightChunk50P2
