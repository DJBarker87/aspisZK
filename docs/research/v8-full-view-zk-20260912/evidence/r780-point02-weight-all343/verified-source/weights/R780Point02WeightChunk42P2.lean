import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk10
import AspisV8R19.R780Point02WeightSharedChunk11
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

namespace AspisV8R19.R780Point02WeightChunk42P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk10
open AspisV8R19.R780Point02WeightSharedChunk11
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

theorem pw2_0757 : pw2 757 = -5*((([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, -2, 4, 2, 2, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 757 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather378, gather378]
  rw [hwe 376 (by omega), hwe 378 (by omega), hwe 380 (by omega), hwo 378 (by omega), hwo 379 (by omega)]
  change -5*(w2 (2*378) - (half*w2 (2*378) + half^2*w2 (2*376) + half^2*w2 (2*380))) + 7*w2 (2*378+1) + 5*(w2 (2*379+1)) = -5*((([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, -2, 4, 2, 2, -2, 1, 2] : List M).prod))
  rw [w2_leaf_752, w2_leaf_756, w2_leaf_757, w2_leaf_759, w2_leaf_760]
#print axioms pw2_0757

theorem pw2_0759 : pw2 759 = -5*((([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, 4, 2, 2, -2, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List M).prod) + half^2*(([1, 1, 2, -2, -3, -1, 2, -2, 1, 2] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 759 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather379, gather379]
  rw [hwe 377 (by omega), hwe 379 (by omega), hwe 381 (by omega), hwo 376 (by omega), hwo 378 (by omega), hwo 379 (by omega), hwo 380 (by omega)]
  change -5*(w2 (2*379) - (half*w2 (2*379) + half^2*w2 (2*377) + half^2*w2 (2*381))) + 7*w2 (2*379+1) + 5*(half^1*w2 (2*378+1) + half^2*w2 (2*376+1) + half^2*w2 (2*380+1)) = -5*((([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, 4, 2, 2, -2, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List M).prod) + half^2*(([1, 1, 2, -2, -3, -1, 2, -2, 1, 2] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod))
  rw [w2_leaf_753, w2_leaf_754, w2_leaf_757, w2_leaf_758, w2_leaf_759, w2_leaf_761, w2_leaf_762]
#print axioms pw2_0759

theorem pw2_0760 : pw2 760 = 7*(([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 760 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather380]
  rw [hwe 380 (by omega), hwe 381 (by omega), hwo 380 (by omega)]
  change 7*w2 (2*380) + 5*(w2 (2*381)) - 5*w2 (2*380+1) = 7*(([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod)
  rw [w2_leaf_760, w2_leaf_761, w2_leaf_762]
#print axioms pw2_0760

theorem pw2_0761 : pw2 761 = -5*((([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, 3, -3, 2, 2, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 761 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather380, gather380]
  rw [hwe 380 (by omega), hwe 382 (by omega), hwo 380 (by omega), hwo 381 (by omega)]
  change -5*(w2 (2*380) - (half*w2 (2*380) + half*w2 (2*382))) + 7*w2 (2*380+1) + 5*(w2 (2*381+1)) = -5*((([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, 3, -3, 2, 2, -2, 1, 2] : List M).prod))
  rw [w2_leaf_760, w2_leaf_761, w2_leaf_763, w2_leaf_764]
#print axioms pw2_0761

theorem pw2_0763 : pw2 763 = -5*((([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, 3, -3, 2, 2, -2, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod) + half^1*(([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 763 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather381, gather381]
  rw [hwe 381 (by omega), hwe 383 (by omega), hwo 380 (by omega), hwo 381 (by omega), hwo 382 (by omega)]
  change -5*(w2 (2*381) - (half*w2 (2*381) + half*w2 (2*383))) + 7*w2 (2*381+1) + 5*(half^1*w2 (2*380+1) + half^1*w2 (2*382+1)) = -5*((([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod) + half*(([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List M).prod))) + 7*(([1, 1, 2, 3, -3, 2, 2, -2, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod) + half^1*(([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List M).prod))
  rw [w2_leaf_761, w2_leaf_762, w2_leaf_763, w2_leaf_765, w2_leaf_766]
#print axioms pw2_0763

theorem pw2_0764 : pw2 764 = 7*(([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 764 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather382]
  rw [hwe 382 (by omega), hwe 383 (by omega), hwo 382 (by omega)]
  change 7*w2 (2*382) + 5*(w2 (2*383)) - 5*w2 (2*382+1) = 7*(([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod) + 5*((([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List M).prod)) - 5*(([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List M).prod)
  rw [w2_leaf_764, w2_leaf_765, w2_leaf_766]
#print axioms pw2_0764

theorem pw2_0765 : pw2 765 = -5*((([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List M).prod) + half^4*(([1, 1, -1, -2, -3, -1, 2, -2, 1, -1] : List M).prod) + half^5*(0) + half^6*(0) + half^7*(0) + half^7*(0))) + 7*(([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, 3, 4, 2, 2, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 765 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather382, gather382]
  rw [hwe 256 (by omega), hwe 320 (by omega), hwe 352 (by omega), hwe 368 (by omega), hwe 376 (by omega), hwe 380 (by omega), hwe 382 (by omega), hwe 384 (by omega), hwo 382 (by omega), hwo 383 (by omega)]
  change -5*(w2 (2*382) - (half*w2 (2*382) + half^2*w2 (2*380) + half^3*w2 (2*376) + half^4*w2 (2*368) + half^5*w2 (2*352) + half^6*w2 (2*320) + half^7*w2 (2*256) + half^7*w2 (2*384))) + 7*w2 (2*382+1) + 5*(w2 (2*383+1)) = -5*((([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod) - (half*(([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List M).prod) + half^4*(([1, 1, -1, -2, -3, -1, 2, -2, 1, -1] : List M).prod) + half^5*(0) + half^6*(0) + half^7*(0) + half^7*(0))) + 7*(([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List M).prod) + 5*((([1, 1, 2, 3, 4, 2, 2, -2, 1, 2] : List M).prod))
  rw [w2_leaf_512, w2_leaf_640, w2_leaf_704, w2_leaf_736, w2_leaf_752, w2_leaf_760, w2_leaf_764, w2_leaf_765, w2_leaf_767, w2_leaf_768]
#print axioms pw2_0765

theorem pw2_0766 : pw2 766 = 7*(([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List M).prod) + half^4*(([1, 1, -1, -2, -3, -1, 2, -2, 1, -1] : List M).prod) + half^5*(0) + half^6*(0) + half^7*(0) + half^7*(0)) - 5*(([1, 1, 2, 3, 4, 2, 2, -2, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 766 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather383]
  rw [hwe 256 (by omega), hwe 320 (by omega), hwe 352 (by omega), hwe 368 (by omega), hwe 376 (by omega), hwe 380 (by omega), hwe 382 (by omega), hwe 383 (by omega), hwe 384 (by omega), hwo 383 (by omega)]
  change 7*w2 (2*383) + 5*(half^1*w2 (2*382) + half^2*w2 (2*380) + half^3*w2 (2*376) + half^4*w2 (2*368) + half^5*w2 (2*352) + half^6*w2 (2*320) + half^7*w2 (2*256) + half^7*w2 (2*384)) - 5*w2 (2*383+1) = 7*(([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod) + half^2*(([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List M).prod) + half^4*(([1, 1, -1, -2, -3, -1, 2, -2, 1, -1] : List M).prod) + half^5*(0) + half^6*(0) + half^7*(0) + half^7*(0)) - 5*(([1, 1, 2, 3, 4, 2, 2, -2, 1, 2] : List M).prod)
  rw [w2_leaf_512, w2_leaf_640, w2_leaf_704, w2_leaf_736, w2_leaf_752, w2_leaf_760, w2_leaf_764, w2_leaf_766, w2_leaf_767, w2_leaf_768]
#print axioms pw2_0766

end
end AspisV8R19.R780Point02WeightChunk42P2
