import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk13
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

namespace AspisV8R19.R780Point02WeightChunk48P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk13
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

theorem pw2_0938 : pw2 938 = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 938 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather469]
  rw [hwe 468 (by omega), hwe 469 (by omega), hwe 470 (by omega), hwo 469 (by omega)]
  change 7*w2 (2*469) + 5*(half^1*w2 (2*468) + half^1*w2 (2*470)) - 5*w2 (2*469+1) = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0)
  rw [w2_leaf_936, w2_leaf_938, w2_leaf_939, w2_leaf_940]
#print axioms pw2_0938

theorem pw2_0940 : pw2 940 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 940 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather470]
  rw [hwe 470 (by omega), hwe 471 (by omega), hwo 470 (by omega)]
  change 7*w2 (2*470) + 5*(w2 (2*471)) - 5*w2 (2*470+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_940, w2_leaf_941, w2_leaf_942]
#print axioms pw2_0940

theorem pw2_0941 : pw2 941 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 941 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather470, gather470]
  rw [hwe 464 (by omega), hwe 468 (by omega), hwe 470 (by omega), hwe 472 (by omega), hwo 470 (by omega), hwo 471 (by omega)]
  change -5*(w2 (2*470) - (half*w2 (2*470) + half^2*w2 (2*468) + half^3*w2 (2*464) + half^3*w2 (2*472))) + 7*w2 (2*470+1) + 5*(w2 (2*471+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_928, w2_leaf_936, w2_leaf_940, w2_leaf_941, w2_leaf_943, w2_leaf_944]
#print axioms pw2_0941

theorem pw2_0942 : pw2 942 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^3*(0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 942 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather471]
  rw [hwe 464 (by omega), hwe 468 (by omega), hwe 470 (by omega), hwe 471 (by omega), hwe 472 (by omega), hwo 471 (by omega)]
  change 7*w2 (2*471) + 5*(half^1*w2 (2*470) + half^2*w2 (2*468) + half^3*w2 (2*464) + half^3*w2 (2*472)) - 5*w2 (2*471+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^3*(0)) - 5*(0)
  rw [w2_leaf_928, w2_leaf_936, w2_leaf_940, w2_leaf_942, w2_leaf_943, w2_leaf_944]
#print axioms pw2_0942

theorem pw2_0944 : pw2 944 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 944 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather472]
  rw [hwe 472 (by omega), hwe 473 (by omega), hwo 472 (by omega)]
  change 7*w2 (2*472) + 5*(w2 (2*473)) - 5*w2 (2*472+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_944, w2_leaf_945, w2_leaf_946]
#print axioms pw2_0944

theorem pw2_0945 : pw2 945 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 945 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather472, gather472]
  rw [hwe 472 (by omega), hwe 474 (by omega), hwo 472 (by omega), hwo 473 (by omega)]
  change -5*(w2 (2*472) - (half*w2 (2*472) + half*w2 (2*474))) + 7*w2 (2*472+1) + 5*(w2 (2*473+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_944, w2_leaf_945, w2_leaf_947, w2_leaf_948]
#print axioms pw2_0945

theorem pw2_0948 : pw2 948 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 948 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather474]
  rw [hwe 474 (by omega), hwe 475 (by omega), hwo 474 (by omega)]
  change 7*w2 (2*474) + 5*(w2 (2*475)) - 5*w2 (2*474+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_948, w2_leaf_949, w2_leaf_950]
#print axioms pw2_0948

theorem pw2_0949 : pw2 949 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 949 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather474, gather474]
  rw [hwe 472 (by omega), hwe 474 (by omega), hwe 476 (by omega), hwo 474 (by omega), hwo 475 (by omega)]
  change -5*(w2 (2*474) - (half*w2 (2*474) + half^2*w2 (2*472) + half^2*w2 (2*476))) + 7*w2 (2*474+1) + 5*(w2 (2*475+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_944, w2_leaf_948, w2_leaf_949, w2_leaf_951, w2_leaf_952]
#print axioms pw2_0949

end
end AspisV8R19.R780Point02WeightChunk48P2
