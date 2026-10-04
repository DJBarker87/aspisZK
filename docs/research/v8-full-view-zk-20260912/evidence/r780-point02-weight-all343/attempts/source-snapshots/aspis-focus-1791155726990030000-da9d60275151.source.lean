import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk12
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

namespace AspisV8R19.R780Point02WeightChunk49P0
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk12
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

theorem pw0_0952 : pw0 952 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 952 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather476]
  rw [hwe 476 (by omega), hwe 477 (by omega), hwo 476 (by omega)]
  change 7*w0 (2*476) + 5*(w0 (2*477)) - 5*w0 (2*476+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_952, w0_leaf_953, w0_leaf_954]
#print axioms pw0_0952

theorem pw0_0953 : pw0 953 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 953 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather476, gather476]
  rw [hwe 476 (by omega), hwe 478 (by omega), hwo 476 (by omega), hwo 477 (by omega)]
  change -5*(w0 (2*476) - (half*w0 (2*476) + half*w0 (2*478))) + 7*w0 (2*476+1) + 5*(w0 (2*477+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_952, w0_leaf_953, w0_leaf_955, w0_leaf_956]
#print axioms pw0_0953

theorem pw0_0954 : pw0 954 = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 954 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather477]
  rw [hwe 476 (by omega), hwe 477 (by omega), hwe 478 (by omega), hwo 477 (by omega)]
  change 7*w0 (2*477) + 5*(half^1*w0 (2*476) + half^1*w0 (2*478)) - 5*w0 (2*477+1) = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0)
  rw [w0_leaf_952, w0_leaf_954, w0_leaf_955, w0_leaf_956]
#print axioms pw0_0954

theorem pw0_0956 : pw0 956 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 956 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather478]
  rw [hwe 478 (by omega), hwe 479 (by omega), hwo 478 (by omega)]
  change 7*w0 (2*478) + 5*(w0 (2*479)) - 5*w0 (2*478+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_956, w0_leaf_957, w0_leaf_958]
#print axioms pw0_0956

theorem pw0_0958 : pw0 958 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^5*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 958 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather479]
  rw [hwe 448 (by omega), hwe 464 (by omega), hwe 472 (by omega), hwe 476 (by omega), hwe 478 (by omega), hwe 479 (by omega), hwe 480 (by omega), hwo 479 (by omega)]
  change 7*w0 (2*479) + 5*(half^1*w0 (2*478) + half^2*w0 (2*476) + half^3*w0 (2*472) + half^4*w0 (2*464) + half^5*w0 (2*448) + half^5*w0 (2*480)) - 5*w0 (2*479+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^5*(0)) - 5*(0)
  rw [w0_leaf_896, w0_leaf_928, w0_leaf_944, w0_leaf_952, w0_leaf_956, w0_leaf_958, w0_leaf_959, w0_leaf_960]
#print axioms pw0_0958

theorem pw0_0960 : pw0 960 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 960 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather480]
  rw [hwe 480 (by omega), hwe 481 (by omega), hwo 480 (by omega)]
  change 7*w0 (2*480) + 5*(w0 (2*481)) - 5*w0 (2*480+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_960, w0_leaf_961, w0_leaf_962]
#print axioms pw0_0960

theorem pw0_0961 : pw0 961 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 961 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather480, gather480]
  rw [hwe 480 (by omega), hwe 482 (by omega), hwo 480 (by omega), hwo 481 (by omega)]
  change -5*(w0 (2*480) - (half*w0 (2*480) + half*w0 (2*482))) + 7*w0 (2*480+1) + 5*(w0 (2*481+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_960, w0_leaf_961, w0_leaf_963, w0_leaf_964]
#print axioms pw0_0961

theorem pw0_0962 : pw0 962 = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 962 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather481]
  rw [hwe 480 (by omega), hwe 481 (by omega), hwe 482 (by omega), hwo 481 (by omega)]
  change 7*w0 (2*481) + 5*(half^1*w0 (2*480) + half^1*w0 (2*482)) - 5*w0 (2*481+1) = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0)
  rw [w0_leaf_960, w0_leaf_962, w0_leaf_963, w0_leaf_964]
#print axioms pw0_0962

end
end AspisV8R19.R780Point02WeightChunk49P0
