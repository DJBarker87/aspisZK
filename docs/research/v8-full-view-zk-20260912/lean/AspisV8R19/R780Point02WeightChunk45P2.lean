import AspisV8R19.R780Point02WeightShared
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

namespace AspisV8R19.R780Point02WeightChunk45P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
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

theorem pw2_0906 : pw2 906 = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 906 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather453]
  rw [hwe 452 (by omega), hwe 453 (by omega), hwe 454 (by omega), hwo 453 (by omega)]
  change 7*w2 (2*453) + 5*(half^1*w2 (2*452) + half^1*w2 (2*454)) - 5*w2 (2*453+1) = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0)
  rw [w2_leaf_904, w2_leaf_906, w2_leaf_907, w2_leaf_908]
#print axioms pw2_0906

theorem pw2_0908 : pw2 908 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 908 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather454]
  rw [hwe 454 (by omega), hwe 455 (by omega), hwo 454 (by omega)]
  change 7*w2 (2*454) + 5*(w2 (2*455)) - 5*w2 (2*454+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_908, w2_leaf_909, w2_leaf_910]
#print axioms pw2_0908

theorem pw2_0909 : pw2 909 = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 909 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather454, gather454]
  rw [hwe 448 (by omega), hwe 452 (by omega), hwe 454 (by omega), hwe 456 (by omega), hwo 454 (by omega), hwo 455 (by omega)]
  change -5*(w2 (2*454) - (half*w2 (2*454) + half^2*w2 (2*452) + half^3*w2 (2*448) + half^3*w2 (2*456))) + 7*w2 (2*454+1) + 5*(w2 (2*455+1)) = -5*((0) - (half*(0) + half^2*(0) + half^3*(0) + half^3*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_896, w2_leaf_904, w2_leaf_908, w2_leaf_909, w2_leaf_911, w2_leaf_912]
#print axioms pw2_0909

theorem pw2_0910 : pw2 910 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^3*(0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 910 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather455]
  rw [hwe 448 (by omega), hwe 452 (by omega), hwe 454 (by omega), hwe 455 (by omega), hwe 456 (by omega), hwo 455 (by omega)]
  change 7*w2 (2*455) + 5*(half^1*w2 (2*454) + half^2*w2 (2*452) + half^3*w2 (2*448) + half^3*w2 (2*456)) - 5*w2 (2*455+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^3*(0) + half^3*(0)) - 5*(0)
  rw [w2_leaf_896, w2_leaf_904, w2_leaf_908, w2_leaf_910, w2_leaf_911, w2_leaf_912]
#print axioms pw2_0910

theorem pw2_0912 : pw2 912 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 912 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather456]
  rw [hwe 456 (by omega), hwe 457 (by omega), hwo 456 (by omega)]
  change 7*w2 (2*456) + 5*(w2 (2*457)) - 5*w2 (2*456+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_912, w2_leaf_913, w2_leaf_914]
#print axioms pw2_0912

theorem pw2_0913 : pw2 913 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 913 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather456, gather456]
  rw [hwe 456 (by omega), hwe 458 (by omega), hwo 456 (by omega), hwo 457 (by omega)]
  change -5*(w2 (2*456) - (half*w2 (2*456) + half*w2 (2*458))) + 7*w2 (2*456+1) + 5*(w2 (2*457+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_912, w2_leaf_913, w2_leaf_915, w2_leaf_916]
#print axioms pw2_0913

theorem pw2_0914 : pw2 914 = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 914 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather457]
  rw [hwe 456 (by omega), hwe 457 (by omega), hwe 458 (by omega), hwo 457 (by omega)]
  change 7*w2 (2*457) + 5*(half^1*w2 (2*456) + half^1*w2 (2*458)) - 5*w2 (2*457+1) = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0)
  rw [w2_leaf_912, w2_leaf_914, w2_leaf_915, w2_leaf_916]
#print axioms pw2_0914

theorem pw2_0916 : pw2 916 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 916 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather458]
  rw [hwe 458 (by omega), hwe 459 (by omega), hwo 458 (by omega)]
  change 7*w2 (2*458) + 5*(w2 (2*459)) - 5*w2 (2*458+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_916, w2_leaf_917, w2_leaf_918]
#print axioms pw2_0916

end
end AspisV8R19.R780Point02WeightChunk45P2
