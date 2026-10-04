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

namespace AspisV8R19.R780Point02WeightChunk41P0
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

theorem pw0_0634 : pw0 634 = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 634 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather317]
  rw [hwe 316 (by omega), hwe 317 (by omega), hwe 318 (by omega), hwo 317 (by omega)]
  change 7*w0 (2*317) + 5*(half^1*w0 (2*316) + half^1*w0 (2*318)) - 5*w0 (2*317+1) = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0)
  rw [w0_leaf_632, w0_leaf_634, w0_leaf_635, w0_leaf_636]
#print axioms pw0_0634

theorem pw0_0636 : pw0 636 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 636 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather318]
  rw [hwe 318 (by omega), hwe 319 (by omega), hwo 318 (by omega)]
  change 7*w0 (2*318) + 5*(w0 (2*319)) - 5*w0 (2*318+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_636, w0_leaf_637, w0_leaf_638]
#print axioms pw0_0636

theorem pw0_0637 : pw0 637 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^6*(0) + half^6*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 637 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather318, gather318]
  rw [hwe 256 (by omega), hwe 288 (by omega), hwe 304 (by omega), hwe 312 (by omega), hwe 316 (by omega), hwe 318 (by omega), hwe 320 (by omega), hwo 318 (by omega), hwo 319 (by omega)]
  change -5*(w0 (2*318) - (half*w0 (2*318) + half^2*w0 (2*316) + half^3*w0 (2*312) + half^4*w0 (2*304) + half^5*w0 (2*288) + half^6*w0 (2*256) + half^6*w0 (2*320))) + 7*w0 (2*318+1) + 5*(w0 (2*319+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^6*(0) + half^6*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_512, w0_leaf_576, w0_leaf_608, w0_leaf_624, w0_leaf_632, w0_leaf_636, w0_leaf_637, w0_leaf_639, w0_leaf_640]
#print axioms pw0_0637

theorem pw0_0638 : pw0 638 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^6*(0) + half^6*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 638 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather319]
  rw [hwe 256 (by omega), hwe 288 (by omega), hwe 304 (by omega), hwe 312 (by omega), hwe 316 (by omega), hwe 318 (by omega), hwe 319 (by omega), hwe 320 (by omega), hwo 319 (by omega)]
  change 7*w0 (2*319) + 5*(half^1*w0 (2*318) + half^2*w0 (2*316) + half^3*w0 (2*312) + half^4*w0 (2*304) + half^5*w0 (2*288) + half^6*w0 (2*256) + half^6*w0 (2*320)) - 5*w0 (2*319+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^6*(0) + half^6*(0)) - 5*(0)
  rw [w0_leaf_512, w0_leaf_576, w0_leaf_608, w0_leaf_624, w0_leaf_632, w0_leaf_636, w0_leaf_638, w0_leaf_639, w0_leaf_640]
#print axioms pw0_0638

theorem pw0_0639 : pw0 639 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^6*(0) + half^6*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^6*(0) + half^6*(0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 639 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather319, gather319]
  rw [hwe 257 (by omega), hwe 289 (by omega), hwe 305 (by omega), hwe 313 (by omega), hwe 317 (by omega), hwe 319 (by omega), hwe 321 (by omega), hwo 256 (by omega), hwo 288 (by omega), hwo 304 (by omega), hwo 312 (by omega), hwo 316 (by omega), hwo 318 (by omega), hwo 319 (by omega), hwo 320 (by omega)]
  change -5*(w0 (2*319) - (half*w0 (2*319) + half^2*w0 (2*317) + half^3*w0 (2*313) + half^4*w0 (2*305) + half^5*w0 (2*289) + half^6*w0 (2*257) + half^6*w0 (2*321))) + 7*w0 (2*319+1) + 5*(half^1*w0 (2*318+1) + half^2*w0 (2*316+1) + half^3*w0 (2*312+1) + half^4*w0 (2*304+1) + half^5*w0 (2*288+1) + half^6*w0 (2*256+1) + half^6*w0 (2*320+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^6*(0) + half^6*(0))) + 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^6*(0) + half^6*(0))
  rw [w0_leaf_513, w0_leaf_514, w0_leaf_577, w0_leaf_578, w0_leaf_609, w0_leaf_610, w0_leaf_625, w0_leaf_626, w0_leaf_633, w0_leaf_634, w0_leaf_637, w0_leaf_638, w0_leaf_639, w0_leaf_641, w0_leaf_642]
#print axioms pw0_0639

theorem pw0_0752 : pw0 752 = 7*(([1, 1, 2, -2, -3, -1, -1, 3, 1, -1] : List M).prod) + 5*((([1, 1, 2, -2, -3, 2, -1, 3, 1, -1] : List M).prod)) - 5*(([1, 1, 2, -2, -3, -1, -1, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w0 7 5 (-5) 752 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather376]
  rw [hwe 376 (by omega), hwe 377 (by omega), hwo 376 (by omega)]
  change 7*w0 (2*376) + 5*(w0 (2*377)) - 5*w0 (2*376+1) = 7*(([1, 1, 2, -2, -3, -1, -1, 3, 1, -1] : List M).prod) + 5*((([1, 1, 2, -2, -3, 2, -1, 3, 1, -1] : List M).prod)) - 5*(([1, 1, 2, -2, -3, -1, -1, 3, 1, 2] : List M).prod)
  rw [w0_leaf_752, w0_leaf_753, w0_leaf_754]
#print axioms pw0_0752

theorem pw0_0755 : pw0 755 = -5*((([1, 1, 2, -2, -3, 2, -1, 3, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, -3, 2, -1, 3, 1, -1] : List M).prod) + half*(([1, 1, 2, -2, 4, 2, -1, 3, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, -3, 2, -1, 3, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, -2, -3, -1, -1, 3, 1, 2] : List M).prod) + half^1*(([1, 1, 2, -2, 4, -1, -1, 3, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w0 7 5 (-5) 755 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather377, gather377]
  rw [hwe 377 (by omega), hwe 379 (by omega), hwo 376 (by omega), hwo 377 (by omega), hwo 378 (by omega)]
  change -5*(w0 (2*377) - (half*w0 (2*377) + half*w0 (2*379))) + 7*w0 (2*377+1) + 5*(half^1*w0 (2*376+1) + half^1*w0 (2*378+1)) = -5*((([1, 1, 2, -2, -3, 2, -1, 3, 1, -1] : List M).prod) - (half*(([1, 1, 2, -2, -3, 2, -1, 3, 1, -1] : List M).prod) + half*(([1, 1, 2, -2, 4, 2, -1, 3, 1, -1] : List M).prod))) + 7*(([1, 1, 2, -2, -3, 2, -1, 3, 1, 2] : List M).prod) + 5*(half^1*(([1, 1, 2, -2, -3, -1, -1, 3, 1, 2] : List M).prod) + half^1*(([1, 1, 2, -2, 4, -1, -1, 3, 1, 2] : List M).prod))
  rw [w0_leaf_753, w0_leaf_754, w0_leaf_755, w0_leaf_757, w0_leaf_758]
#print axioms pw0_0755

theorem pw0_0756 : pw0 756 = 7*(([1, 1, 2, -2, 4, -1, -1, 3, 1, -1] : List M).prod) + 5*((([1, 1, 2, -2, 4, 2, -1, 3, 1, -1] : List M).prod)) - 5*(([1, 1, 2, -2, 4, -1, -1, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w0 7 5 (-5) 756 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather378]
  rw [hwe 378 (by omega), hwe 379 (by omega), hwo 378 (by omega)]
  change 7*w0 (2*378) + 5*(w0 (2*379)) - 5*w0 (2*378+1) = 7*(([1, 1, 2, -2, 4, -1, -1, 3, 1, -1] : List M).prod) + 5*((([1, 1, 2, -2, 4, 2, -1, 3, 1, -1] : List M).prod)) - 5*(([1, 1, 2, -2, 4, -1, -1, 3, 1, 2] : List M).prod)
  rw [w0_leaf_756, w0_leaf_757, w0_leaf_758]
#print axioms pw0_0756

end
end AspisV8R19.R780Point02WeightChunk41P0
