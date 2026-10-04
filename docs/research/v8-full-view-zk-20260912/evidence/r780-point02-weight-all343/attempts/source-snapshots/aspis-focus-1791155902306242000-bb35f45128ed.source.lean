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

namespace AspisV8R19.R780Point02WeightChunk51P0
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

theorem pw0_0974 : pw0 974 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^3*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 974 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather487]
  rw [hwe 480 (by omega), hwe 484 (by omega), hwe 486 (by omega), hwe 487 (by omega), hwe 488 (by omega), hwo 487 (by omega)]
  change 7*w0 (2*487) + 5*(half^1*w0 (2*486) + half^2*w0 (2*484) + half^3*w0 (2*480) + half^3*w0 (2*488)) - 5*w0 (2*487+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^3*(0)) - 5*(0)
  rw [w0_leaf_960, w0_leaf_968, w0_leaf_972, w0_leaf_974, w0_leaf_975, w0_leaf_976]
#print axioms pw0_0974

theorem pw0_0976 : pw0 976 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 976 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather488]
  rw [hwe 488 (by omega), hwe 489 (by omega), hwo 488 (by omega)]
  change 7*w0 (2*488) + 5*(w0 (2*489)) - 5*w0 (2*488+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_976, w0_leaf_977, w0_leaf_978]
#print axioms pw0_0976

theorem pw0_0977 : pw0 977 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 977 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather488, gather488]
  rw [hwe 488 (by omega), hwe 490 (by omega), hwo 488 (by omega), hwo 489 (by omega)]
  change -5*(w0 (2*488) - (half*w0 (2*488) + half*w0 (2*490))) + 7*w0 (2*488+1) + 5*(w0 (2*489+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_976, w0_leaf_977, w0_leaf_979, w0_leaf_980]
#print axioms pw0_0977

theorem pw0_0978 : pw0 978 = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 978 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather489]
  rw [hwe 488 (by omega), hwe 489 (by omega), hwe 490 (by omega), hwo 489 (by omega)]
  change 7*w0 (2*489) + 5*(half^1*w0 (2*488) + half^1*w0 (2*490)) - 5*w0 (2*489+1) = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0)
  rw [w0_leaf_976, w0_leaf_978, w0_leaf_979, w0_leaf_980]
#print axioms pw0_0978

theorem pw0_0980 : pw0 980 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 980 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather490]
  rw [hwe 490 (by omega), hwe 491 (by omega), hwo 490 (by omega)]
  change 7*w0 (2*490) + 5*(w0 (2*491)) - 5*w0 (2*490+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_980, w0_leaf_981, w0_leaf_982]
#print axioms pw0_0980

theorem pw0_0981 : pw0 981 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 981 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather490, gather490]
  rw [hwe 488 (by omega), hwe 490 (by omega), hwe 492 (by omega), hwo 490 (by omega), hwo 491 (by omega)]
  change -5*(w0 (2*490) - (half*w0 (2*490) + half^2*w0 (2*488) + half^2*w0 (2*492))) + 7*w0 (2*490+1) + 5*(w0 (2*491+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_976, w0_leaf_980, w0_leaf_981, w0_leaf_983, w0_leaf_984]
#print axioms pw0_0981

theorem pw0_0982 : pw0 982 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 982 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather491]
  rw [hwe 488 (by omega), hwe 490 (by omega), hwe 491 (by omega), hwe 492 (by omega), hwo 491 (by omega)]
  change 7*w0 (2*491) + 5*(half^1*w0 (2*490) + half^2*w0 (2*488) + half^2*w0 (2*492)) - 5*w0 (2*491+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0)
  rw [w0_leaf_976, w0_leaf_980, w0_leaf_982, w0_leaf_983, w0_leaf_984]
#print axioms pw0_0982

theorem pw0_0984 : pw0 984 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 984 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather492]
  rw [hwe 492 (by omega), hwe 493 (by omega), hwo 492 (by omega)]
  change 7*w0 (2*492) + 5*(w0 (2*493)) - 5*w0 (2*492+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_984, w0_leaf_985, w0_leaf_986]
#print axioms pw0_0984

end
end AspisV8R19.R780Point02WeightChunk51P0
