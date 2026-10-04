import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R780Point02WeightSharedChunk11
import AspisV8R19.R780Point02WeightSharedChunk12
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

namespace AspisV8R19.R780Point02WeightChunk44P0
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightSharedChunk11
open AspisV8R19.R780Point02WeightSharedChunk12
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

theorem pw0_0892 : pw0 892 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 892 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather446]
  rw [hwe 446 (by omega), hwe 447 (by omega), hwo 446 (by omega)]
  change 7*w0 (2*446) + 5*(w0 (2*447)) - 5*w0 (2*446+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_892, w0_leaf_893, w0_leaf_894]
#print axioms pw0_0892

theorem pw0_0893 : pw0 893 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^6*(0) + half^6*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 893 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather446, gather446]
  rw [hwe 384 (by omega), hwe 416 (by omega), hwe 432 (by omega), hwe 440 (by omega), hwe 444 (by omega), hwe 446 (by omega), hwe 448 (by omega), hwo 446 (by omega), hwo 447 (by omega)]
  change -5*(w0 (2*446) - (half*w0 (2*446) + half^2*w0 (2*444) + half^3*w0 (2*440) + half^4*w0 (2*432) + half^5*w0 (2*416) + half^6*w0 (2*384) + half^6*w0 (2*448))) + 7*w0 (2*446+1) + 5*(w0 (2*447+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^6*(0) + half^6*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_768, w0_leaf_832, w0_leaf_864, w0_leaf_880, w0_leaf_888, w0_leaf_892, w0_leaf_893, w0_leaf_895, w0_leaf_896]
#print axioms pw0_0893

theorem pw0_0894 : pw0 894 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^6*(0) + half^6*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 894 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather447]
  rw [hwe 384 (by omega), hwe 416 (by omega), hwe 432 (by omega), hwe 440 (by omega), hwe 444 (by omega), hwe 446 (by omega), hwe 447 (by omega), hwe 448 (by omega), hwo 447 (by omega)]
  change 7*w0 (2*447) + 5*(half^1*w0 (2*446) + half^2*w0 (2*444) + half^3*w0 (2*440) + half^4*w0 (2*432) + half^5*w0 (2*416) + half^6*w0 (2*384) + half^6*w0 (2*448)) - 5*w0 (2*447+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^4*(0) + half^5*(0) + half^6*(0) + half^6*(0)) - 5*(0)
  rw [w0_leaf_768, w0_leaf_832, w0_leaf_864, w0_leaf_880, w0_leaf_888, w0_leaf_892, w0_leaf_894, w0_leaf_895, w0_leaf_896]
#print axioms pw0_0894

theorem pw0_0900 : pw0 900 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 900 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather450]
  rw [hwe 450 (by omega), hwe 451 (by omega), hwo 450 (by omega)]
  change 7*w0 (2*450) + 5*(w0 (2*451)) - 5*w0 (2*450+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_900, w0_leaf_901, w0_leaf_902]
#print axioms pw0_0900

theorem pw0_0901 : pw0 901 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 901 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather450, gather450]
  rw [hwe 448 (by omega), hwe 450 (by omega), hwe 452 (by omega), hwo 450 (by omega), hwo 451 (by omega)]
  change -5*(w0 (2*450) - (half*w0 (2*450) + half^2*w0 (2*448) + half^2*w0 (2*452))) + 7*w0 (2*450+1) + 5*(w0 (2*451+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_896, w0_leaf_900, w0_leaf_901, w0_leaf_903, w0_leaf_904]
#print axioms pw0_0901

theorem pw0_0902 : pw0 902 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 902 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather451]
  rw [hwe 448 (by omega), hwe 450 (by omega), hwe 451 (by omega), hwe 452 (by omega), hwo 451 (by omega)]
  change 7*w0 (2*451) + 5*(half^1*w0 (2*450) + half^2*w0 (2*448) + half^2*w0 (2*452)) - 5*w0 (2*451+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0)
  rw [w0_leaf_896, w0_leaf_900, w0_leaf_902, w0_leaf_903, w0_leaf_904]
#print axioms pw0_0902

theorem pw0_0904 : pw0 904 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w0 7 5 (-5) 904 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather452]
  rw [hwe 452 (by omega), hwe 453 (by omega), hwo 452 (by omega)]
  change 7*w0 (2*452) + 5*(w0 (2*453)) - 5*w0 (2*452+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w0_leaf_904, w0_leaf_905, w0_leaf_906]
#print axioms pw0_0904

theorem pw0_0905 : pw0 905 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w0 7 5 (-5) 905 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather452, gather452]
  rw [hwe 452 (by omega), hwe 454 (by omega), hwo 452 (by omega), hwo 453 (by omega)]
  change -5*(w0 (2*452) - (half*w0 (2*452) + half*w0 (2*454))) + 7*w0 (2*452+1) + 5*(w0 (2*453+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w0_leaf_904, w0_leaf_905, w0_leaf_907, w0_leaf_908]
#print axioms pw0_0905

end
end AspisV8R19.R780Point02WeightChunk44P0
