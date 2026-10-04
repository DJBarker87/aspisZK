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

namespace AspisV8R19.R780Point02WeightChunk43P2
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

theorem pw2_0880 : pw2 880 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 880 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather440]
  rw [hwe 440 (by omega), hwe 441 (by omega), hwo 440 (by omega)]
  change 7*w2 (2*440) + 5*(w2 (2*441)) - 5*w2 (2*440+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_880, w2_leaf_881, w2_leaf_882]
#print axioms pw2_0880

theorem pw2_0882 : pw2 882 = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 882 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather441]
  rw [hwe 440 (by omega), hwe 441 (by omega), hwe 442 (by omega), hwo 441 (by omega)]
  change 7*w2 (2*441) + 5*(half^1*w2 (2*440) + half^1*w2 (2*442)) - 5*w2 (2*441+1) = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0)
  rw [w2_leaf_880, w2_leaf_882, w2_leaf_883, w2_leaf_884]
#print axioms pw2_0882

theorem pw2_0884 : pw2 884 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 884 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather442]
  rw [hwe 442 (by omega), hwe 443 (by omega), hwo 442 (by omega)]
  change 7*w2 (2*442) + 5*(w2 (2*443)) - 5*w2 (2*442+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_884, w2_leaf_885, w2_leaf_886]
#print axioms pw2_0884

theorem pw2_0885 : pw2 885 = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 885 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather442, gather442]
  rw [hwe 440 (by omega), hwe 442 (by omega), hwe 444 (by omega), hwo 442 (by omega), hwo 443 (by omega)]
  change -5*(w2 (2*442) - (half*w2 (2*442) + half^2*w2 (2*440) + half^2*w2 (2*444))) + 7*w2 (2*442+1) + 5*(w2 (2*443+1)) = -5*((0) - (half*(0) + half^2*(0) + half^2*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_880, w2_leaf_884, w2_leaf_885, w2_leaf_887, w2_leaf_888]
#print axioms pw2_0885

theorem pw2_0886 : pw2 886 = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 886 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather443]
  rw [hwe 440 (by omega), hwe 442 (by omega), hwe 443 (by omega), hwe 444 (by omega), hwo 443 (by omega)]
  change 7*w2 (2*443) + 5*(half^1*w2 (2*442) + half^2*w2 (2*440) + half^2*w2 (2*444)) - 5*w2 (2*443+1) = 7*(0) + 5*(half^1*(0) + half^2*(0) + half^2*(0)) - 5*(0)
  rw [w2_leaf_880, w2_leaf_884, w2_leaf_886, w2_leaf_887, w2_leaf_888]
#print axioms pw2_0886

theorem pw2_0888 : pw2 888 = 7*(0) + 5*((0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 888 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather444]
  rw [hwe 444 (by omega), hwe 445 (by omega), hwo 444 (by omega)]
  change 7*w2 (2*444) + 5*(w2 (2*445)) - 5*w2 (2*444+1) = 7*(0) + 5*((0)) - 5*(0)
  rw [w2_leaf_888, w2_leaf_889, w2_leaf_890]
#print axioms pw2_0888

theorem pw2_0889 : pw2 889 = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0)) := by
  change sourceChordTranspose half w2 7 5 (-5) 889 = _
  unfold sourceChordTranspose interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gatherGather444, gather444]
  rw [hwe 444 (by omega), hwe 446 (by omega), hwo 444 (by omega), hwo 445 (by omega)]
  change -5*(w2 (2*444) - (half*w2 (2*444) + half*w2 (2*446))) + 7*w2 (2*444+1) + 5*(w2 (2*445+1)) = -5*((0) - (half*(0) + half*(0))) + 7*(0) + 5*((0))
  rw [w2_leaf_888, w2_leaf_889, w2_leaf_891, w2_leaf_892]
#print axioms pw2_0889

theorem pw2_0890 : pw2 890 = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0) := by
  change sourceChordTranspose half w2 7 5 (-5) 890 = _
  unfold sourceChordTranspose interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [gather445]
  rw [hwe 444 (by omega), hwe 445 (by omega), hwe 446 (by omega), hwo 445 (by omega)]
  change 7*w2 (2*445) + 5*(half^1*w2 (2*444) + half^1*w2 (2*446)) - 5*w2 (2*445+1) = 7*(0) + 5*(half^1*(0) + half^1*(0)) - 5*(0)
  rw [w2_leaf_888, w2_leaf_890, w2_leaf_891, w2_leaf_892]
#print axioms pw2_0890

end
end AspisV8R19.R780Point02WeightChunk43P2
