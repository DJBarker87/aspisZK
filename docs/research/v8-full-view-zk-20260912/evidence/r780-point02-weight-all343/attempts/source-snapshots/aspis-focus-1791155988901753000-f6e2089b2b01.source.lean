import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk14
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

namespace AspisV8R19.R780Point02WeightChunk52P0
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk14
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

theorem pw0_0985 : pw0 985 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 985 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather492, gather492]
  rw [hwe 492 (by omega), hwe 494 (by omega), hwo 492 (by omega), hwo 493 (by omega)]
  change -5*(w0 (2*492) - (half*w0 (2*492) + half*w0 (2*494))) + 7*w0 (2*492+1) + 5*(w0 (2*493+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_984, w0_leaf_985, w0_leaf_987, w0_leaf_988]
#print axioms pw0_0985

theorem pw0_0986 : pw0 986 = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 986 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather493]
  rw [hwe 492 (by omega), hwe 493 (by omega), hwe 494 (by omega), hwo 493 (by omega)]
  change 7*w0 (2*493) + 5*(half^1*w0 (2*492) + half^1*w0 (2*494)) - 5*w0 (2*493+1) = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0)
  rw [w0_leaf_984, w0_leaf_986, w0_leaf_987, w0_leaf_988]
#print axioms pw0_0986

theorem pw0_0988 : pw0 988 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 988 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather494]
  rw [hwe 494 (by omega), hwe 495 (by omega), hwo 494 (by omega)]
  change 7*w0 (2*494) + 5*(w0 (2*495)) - 5*w0 (2*494+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_988, w0_leaf_989, w0_leaf_990]
#print axioms pw0_0988

theorem pw0_0989 : pw0 989 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 989 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather494, gather494]
  rw [hwe 480 (by omega), hwe 488 (by omega), hwe 492 (by omega), hwe 494 (by omega), hwe 496 (by omega), hwo 494 (by omega), hwo 495 (by omega)]
  change -5*(w0 (2*494) - (half*w0 (2*494) + half^2*w0 (2*492) + half^3*w0 (2*488) + half^4*w0 (2*480) + half^4*w0 (2*496))) + 7*w0 (2*494+1) + 5*(w0 (2*495+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod))) + 7*(0) + 5*((0))
  rw [w0_leaf_960, w0_leaf_976, w0_leaf_984, w0_leaf_988, w0_leaf_989, w0_leaf_991, w0_leaf_992]
#print axioms pw0_0989

theorem pw0_0990 : pw0 990 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 990 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather495]
  rw [hwe 480 (by omega), hwe 488 (by omega), hwe 492 (by omega), hwe 494 (by omega), hwe 495 (by omega), hwe 496 (by omega), hwo 495 (by omega)]
  change 7*w0 (2*495) + 5*(half^1*w0 (2*494) + half^2*w0 (2*492) + half^3*w0 (2*488) + half^4*w0 (2*480) + half^4*w0 (2*496)) - 5*w0 (2*495+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod)) - 5*(0)
  rw [w0_leaf_960, w0_leaf_976, w0_leaf_984, w0_leaf_988, w0_leaf_990, w0_leaf_991, w0_leaf_992]
#print axioms pw0_0990

theorem pw0_0992 : pw0 992 = 7*(([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + 5*((([1, 1, -1, -2, -3, 2, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, -1, -2, -3, -1, -1, -2, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w0 7 5 (-5) 992 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather496]
  rw [hwe 496 (by omega), hwe 497 (by omega), hwo 496 (by omega)]
  change 7*w0 (2*496) + 5*(w0 (2*497)) - 5*w0 (2*496+1) = 7*(([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + 5*((([1, 1, -1, -2, -3, 2, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, -1, -2, -3, -1, -1, -2, 1, 2] : List M).prod)
  rw [w0_leaf_992, w0_leaf_993, w0_leaf_994]
#print axioms pw0_0992

theorem pw0_0993 : pw0 993 = -5*((([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + half*(([1, 1, -1, -2, 4, -1, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, -1, -2, -3, -1, -1, -2, 1, 2] : List M).prod) + 5*((([1, 1, -1, -2, -3, 2, -1, -2, 1, 2] : List M).prod)) := by
  change sourceChordTranspose half w0 7 5 (-5) 993 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather496, gather496]
  rw [hwe 496 (by omega), hwe 498 (by omega), hwo 496 (by omega), hwo 497 (by omega)]
  change -5*(w0 (2*496) - (half*w0 (2*496) + half*w0 (2*498))) + 7*w0 (2*496+1) + 5*(w0 (2*497+1)) = -5*((([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod) - (half*(([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + half*(([1, 1, -1, -2, 4, -1, -1, -2, 1, -1] : List M).prod))) + 7*(([1, 1, -1, -2, -3, -1, -1, -2, 1, 2] : List M).prod) + 5*((([1, 1, -1, -2, -3, 2, -1, -2, 1, 2] : List M).prod))
  rw [w0_leaf_992, w0_leaf_993, w0_leaf_995, w0_leaf_996]
#print axioms pw0_0993

theorem pw0_0994 : pw0 994 = 7*(([1, 1, -1, -2, -3, 2, -1, -2, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + half^1*(([1, 1, -1, -2, 4, -1, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, -1, -2, -3, 2, -1, -2, 1, 2] : List M).prod) := by
  change sourceChordTranspose half w0 7 5 (-5) 994 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather497]
  rw [hwe 496 (by omega), hwe 497 (by omega), hwe 498 (by omega), hwo 497 (by omega)]
  change 7*w0 (2*497) + 5*(half^1*w0 (2*496) + half^1*w0 (2*498)) - 5*w0 (2*497+1) = 7*(([1, 1, -1, -2, -3, 2, -1, -2, 1, -1] : List M).prod) + 5*(half^1*(([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod) + half^1*(([1, 1, -1, -2, 4, -1, -1, -2, 1, -1] : List M).prod)) - 5*(([1, 1, -1, -2, -3, 2, -1, -2, 1, 2] : List M).prod)
  rw [w0_leaf_992, w0_leaf_994, w0_leaf_995, w0_leaf_996]
#print axioms pw0_0994

end
end AspisV8R19.R780Point02WeightChunk52P0
