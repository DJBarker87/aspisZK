import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk15
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

namespace AspisV8R19.R780Point02WeightChunk53P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk15
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

theorem pw2_0996 : pw2 996 = 7*(([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, -1, -2, 4, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, -2, 4, -1, 2, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 996 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather498]
  rw [hwe 498 (by omega), hwe 499 (by omega), hwo 498 (by omega)]
  change 7*w2 (2*498) + 5*(w2 (2*499)) - 5*w2 (2*498+1) = 7*(([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, -1, -2, 4, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, -2, 4, -1, 2, 3, 1, 2] : List M).prod)
  rw [w2_leaf_996, w2_leaf_997, w2_leaf_998]
#print axioms pw2_0996

theorem pw2_0997 : pw2 997 = -5*((([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, -1, -2, 4, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, -1, -2, 4, 2, 2, 3, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 997 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather498, gather498]
  rw [hwe 496 (by omega), hwe 498 (by omega), hwe 500 (by omega), hwo 498 (by omega), hwo 499 (by omega)]
  change -5*(w2 (2*498) - (half*w2 (2*498) + half^2*w2 (2*496) + half^2*w2 (2*500))) + 7*w2 (2*498+1) + 5*(w2 (2*499+1)) = -5*((([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, -1, -2, 4, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, -1, -2, 4, 2, 2, 3, 1, 2] : List M).prod))
  rw [w2_leaf_992, w2_leaf_996, w2_leaf_997, w2_leaf_999, w2_leaf_1000]
#print axioms pw2_0997

theorem pw2_0998 : pw2 998 = 7*(([1, 1, -1, -2, 4, 2, 2, 3, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, -2, 4, 2, 2, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 998 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather499]
  rw [hwe 496 (by omega), hwe 498 (by omega), hwe 499 (by omega), hwe 500 (by omega), hwo 499 (by omega)]
  change 7*w2 (2*499) + 5*(half^1*w2 (2*498) + half^2*w2 (2*496) + half^2*w2 (2*500)) - 5*w2 (2*499+1) = 7*(([1, 1, -1, -2, 4, 2, 2, 3, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, -2, 4, 2, 2, 3, 1, 2] : List M).prod)
  rw [w2_leaf_992, w2_leaf_996, w2_leaf_998, w2_leaf_999, w2_leaf_1000]
#print axioms pw2_0998

theorem pw2_1000 : pw2 1000 = 7*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, -1, 3, -3, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, -3, -1, 2, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 1000 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather500]
  rw [hwe 500 (by omega), hwe 501 (by omega), hwo 500 (by omega)]
  change 7*w2 (2*500) + 5*(w2 (2*501)) - 5*w2 (2*500+1) = 7*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, -1, 3, -3, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, -3, -1, 2, 3, 1, 2] : List M).prod)
  rw [w2_leaf_1000, w2_leaf_1001, w2_leaf_1002]
#print axioms pw2_1000

theorem pw2_1001 : pw2 1001 = -5*((([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + half*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, -1, 3, -3, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, -1, 3, -3, 2, 2, 3, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 1001 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather500, gather500]
  rw [hwe 500 (by omega), hwe 502 (by omega), hwo 500 (by omega), hwo 501 (by omega)]
  change -5*(w2 (2*500) - (half*w2 (2*500) + half*w2 (2*502))) + 7*w2 (2*500+1) + 5*(w2 (2*501+1)) = -5*((([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + half*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, -1, 3, -3, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, -1, 3, -3, 2, 2, 3, 1, 2] : List M).prod))
  rw [w2_leaf_1000, w2_leaf_1001, w2_leaf_1003, w2_leaf_1004]
#print axioms pw2_1001

theorem pw2_1002 : pw2 1002 = 7*(([1, 1, -1, 3, -3, 2, 2, 3, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + half^1*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, -3, 2, 2, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 1002 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather501]
  rw [hwe 500 (by omega), hwe 501 (by omega), hwe 502 (by omega), hwo 501 (by omega)]
  change 7*w2 (2*501) + 5*(half^1*w2 (2*500) + half^1*w2 (2*502)) - 5*w2 (2*501+1) = 7*(([1, 1, -1, 3, -3, 2, 2, 3, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + half^1*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, -3, 2, 2, 3, 1, 2] : List M).prod)
  rw [w2_leaf_1000, w2_leaf_1002, w2_leaf_1003, w2_leaf_1004]
#print axioms pw2_1002

theorem pw2_1004 : pw2 1004 = 7*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, -1, 3, 4, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, 4, -1, 2, 3, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w2 7 5 (-5) 1004 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather502]
  rw [hwe 502 (by omega), hwe 503 (by omega), hwo 502 (by omega)]
  change 7*w2 (2*502) + 5*(w2 (2*503)) - 5*w2 (2*502+1) = 7*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod) + 5*((([1, 1, -1, 3, 4, 2, 2, 3, 1, -1] : List M).prod)) - 5*(([1, 1, -1, 3, 4, -1, 2, 3, 1, 2] : List M).prod)
  rw [w2_leaf_1004, w2_leaf_1005, w2_leaf_1006]
#print axioms pw2_1004

theorem pw2_1005 : pw2 1005 = -5*((([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + half^3*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, -1, 3, 4, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, -1, 3, 4, 2, 2, 3, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w2 7 5 (-5) 1005 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather502, gather502]
  rw [hwe 496 (by omega), hwe 500 (by omega), hwe 502 (by omega), hwe 504 (by omega), hwo 502 (by omega), hwo 503 (by omega)]
  change -5*(w2 (2*502) - (half*w2 (2*502) + half^2*w2 (2*500) + half^3*w2 (2*496) + half^3*w2 (2*504))) + 7*w2 (2*502+1) + 5*(w2 (2*503+1)) = -5*((([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod) - (half*(([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod) + half^2*(([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod) + half^3*(([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod) + half^3*(([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod))) + 7*(([1, 1, -1, 3, 4, -1, 2, 3, 1, 2] : List M).prod) + 5*((([1, 1, -1, 3, 4, 2, 2, 3, 1, 2] : List M).prod))
  rw [w2_leaf_992, w2_leaf_1000, w2_leaf_1004, w2_leaf_1005, w2_leaf_1007, w2_leaf_1008]
#print axioms pw2_1005

end
end AspisV8R19.R780Point02WeightChunk53P2
