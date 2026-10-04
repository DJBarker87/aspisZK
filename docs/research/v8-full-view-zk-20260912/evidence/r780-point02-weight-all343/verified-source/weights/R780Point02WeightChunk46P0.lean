import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk12
import AspisV8R19.R780Point02WeightSharedChunk13
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

namespace AspisV8R19.R780Point02WeightChunk46P0
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk12
open AspisV8R19.R780Point02WeightSharedChunk13
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

theorem pw0_0917 : pw0 917 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 917 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather458, gather458]
  rw [hwe 456 (by omega), hwe 458 (by omega), hwe 460 (by omega), hwo 458 (by omega), hwo 459 (by omega)]
  change -5*(w0 (2*458) - (half*w0 (2*458) + half^2*w0 (2*456) + half^2*w0 (2*460))) + 7*w0 (2*458+1) + 5*(w0 (2*459+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_912, w0_leaf_916, w0_leaf_917, w0_leaf_919, w0_leaf_920]
#print axioms pw0_0917

theorem pw0_0918 : pw0 918 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 918 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather459]
  rw [hwe 456 (by omega), hwe 458 (by omega), hwe 459 (by omega), hwe 460 (by omega), hwo 459 (by omega)]
  change 7*w0 (2*459) + 5*(half^1*w0 (2*458) + half^2*w0 (2*456) + half^2*w0 (2*460)) - 5*w0 (2*459+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0)
  rw [w0_leaf_912, w0_leaf_916, w0_leaf_918, w0_leaf_919, w0_leaf_920]
#print axioms pw0_0918

theorem pw0_0920 : pw0 920 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 920 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather460]
  rw [hwe 460 (by omega), hwe 461 (by omega), hwo 460 (by omega)]
  change 7*w0 (2*460) + 5*(w0 (2*461)) - 5*w0 (2*460+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_920, w0_leaf_921, w0_leaf_922]
#print axioms pw0_0920

theorem pw0_0921 : pw0 921 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 921 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather460, gather460]
  rw [hwe 460 (by omega), hwe 462 (by omega), hwo 460 (by omega), hwo 461 (by omega)]
  change -5*(w0 (2*460) - (half*w0 (2*460) + half*w0 (2*462))) + 7*w0 (2*460+1) + 5*(w0 (2*461+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_920, w0_leaf_921, w0_leaf_923, w0_leaf_924]
#print axioms pw0_0921

theorem pw0_0922 : pw0 922 = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 922 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather461]
  rw [hwe 460 (by omega), hwe 461 (by omega), hwe 462 (by omega), hwo 461 (by omega)]
  change 7*w0 (2*461) + 5*(half^1*w0 (2*460) + half^1*w0 (2*462)) - 5*w0 (2*461+1) = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0)
  rw [w0_leaf_920, w0_leaf_922, w0_leaf_923, w0_leaf_924]
#print axioms pw0_0922

theorem pw0_0924 : pw0 924 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 924 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather462]
  rw [hwe 462 (by omega), hwe 463 (by omega), hwo 462 (by omega)]
  change 7*w0 (2*462) + 5*(w0 (2*463)) - 5*w0 (2*462+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_924, w0_leaf_925, w0_leaf_926]
#print axioms pw0_0924

theorem pw0_0925 : pw0 925 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 925 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather462, gather462]
  rw [hwe 448 (by omega), hwe 456 (by omega), hwe 460 (by omega), hwe 462 (by omega), hwe 464 (by omega), hwo 462 (by omega), hwo 463 (by omega)]
  change -5*(w0 (2*462) - (half*w0 (2*462) + half^2*w0 (2*460) + half^3*w0 (2*456) + half^4*w0 (2*448) + half^4*w0 (2*464))) + 7*w0 (2*462+1) + 5*(w0 (2*463+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_896, w0_leaf_912, w0_leaf_920, w0_leaf_924, w0_leaf_925, w0_leaf_927, w0_leaf_928]
#print axioms pw0_0925

theorem pw0_0926 : pw0 926 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 926 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather463]
  rw [hwe 448 (by omega), hwe 456 (by omega), hwe 460 (by omega), hwe 462 (by omega), hwe 463 (by omega), hwe 464 (by omega), hwo 463 (by omega)]
  change 7*w0 (2*463) + 5*(half^1*w0 (2*462) + half^2*w0 (2*460) + half^3*w0 (2*456) + half^4*w0 (2*448) + half^4*w0 (2*464)) - 5*w0 (2*463+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^4*(0)) - 5*(0)
  rw [w0_leaf_896, w0_leaf_912, w0_leaf_920, w0_leaf_924, w0_leaf_926, w0_leaf_927, w0_leaf_928]
#print axioms pw0_0926

end
end AspisV8R19.R780Point02WeightChunk46P0
