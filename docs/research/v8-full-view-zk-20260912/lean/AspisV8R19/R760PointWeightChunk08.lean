import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.Point1GuardedChunk00
import AspisV8R19.Point1GuardedChunk01
import AspisV8R19.Point1GuardedChunk02
import AspisV8R19.Point1GuardedChunk03
import AspisV8R19.Point1GuardedChunk04
import AspisV8R19.Point1GuardedChunk05
import AspisV8R19.Point1GuardedChunk06
import AspisV8R19.Point1GuardedChunk07
import AspisV8R19.Point1GuardedChunk08
import AspisV8R19.Point1GuardedChunk09
import AspisV8R19.R759Point1TransportChunk00
import AspisV8R19.R759Point1TransportChunk01
import AspisV8R19.R759Point1TransportChunk02
import AspisV8R19.R759Point1TransportChunk03
import AspisV8R19.R759Point1TransportChunk04
import AspisV8R19.R759Point1TransportChunk05
import AspisV8R19.R759Point1TransportChunk06
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

namespace AspisV8R19.R760PointWeightChunk08
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R748SchedulePrototype
open AspisV8R19.R748GatherExpand00 AspisV8R19.R748GatherExpand01 AspisV8R19.R748GatherExpand02 AspisV8R19.R748GatherExpand03 AspisV8R19.R748GatherExpand04 AspisV8R19.R748GatherExpand05 AspisV8R19.R748GatherExpand06 AspisV8R19.R748GatherExpand07
open AspisV8R19.R748GatherNested00 AspisV8R19.R748GatherNested01 AspisV8R19.R748GatherNested02 AspisV8R19.R748GatherNested03 AspisV8R19.R748GatherNested04
open AspisR19.R754Point1GuardedLeaves
open AspisR19.R759Point1TransportLeaves
open AspisV8R19.R748FiniteGatherSchedules
noncomputable section
set_option maxRecDepth 4096

/-- finite source-only pointWeight expansion at 908; no field reduction --/
lemma pw_0908 : pw 908 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather454]
  rw [hwe 454 (by omega), hwe 455 (by omega), hwo 454 (by omega)]
  change 7*w (2*454) + 5*(w (2*455)) - 5*w (2*454+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0908, w_guarded_leaf_0909, w_guarded_leaf_0910]
#print axioms pw_0908

/-- finite source-only pointWeight expansion at 909; no field reduction --/
lemma pw_0909 : pw 909 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^3*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gatherGather454, gather454]
  rw [hwe 448 (by omega), hwe 452 (by omega), hwe 454 (by omega), hwe 456 (by omega), hwo 454 (by omega), hwo 455 (by omega)]
  change -5*(w (2*454) - ((1073741824:M)*w (2*454) + (1073741824:M)^2*w (2*452) + (1073741824:M)^3*w (2*448) + (1073741824:M)^3*w (2*456))) + 7*w (2*454+1) + 5*(w (2*455+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^3*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0896, w_guarded_leaf_0904, w_guarded_leaf_0908, w_guarded_leaf_0909, w_guarded_leaf_0911, w_guarded_leaf_0912]
#print axioms pw_0909

/-- finite source-only pointWeight expansion at 910; no field reduction --/
lemma pw_0910 : pw 910 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((576 : M)) + ((1073741824:M)^3)*((0 : M))) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather455]
  rw [hwe 448 (by omega), hwe 452 (by omega), hwe 454 (by omega), hwe 455 (by omega), hwe 456 (by omega), hwo 455 (by omega)]
  change 7*w (2*455) + 5*(((1073741824:M)^1)*w (2*454) + ((1073741824:M)^2)*w (2*452) + ((1073741824:M)^3)*w (2*448) + ((1073741824:M)^3)*w (2*456)) - 5*w (2*455+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((576 : M)) + ((1073741824:M)^3)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0896, w_guarded_leaf_0904, w_guarded_leaf_0908, w_guarded_leaf_0910, w_guarded_leaf_0911, w_guarded_leaf_0912]
#print axioms pw_0910

/-- finite source-only pointWeight expansion at 912; no field reduction --/
lemma pw_0912 : pw 912 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather456]
  rw [hwe 456 (by omega), hwe 457 (by omega), hwo 456 (by omega)]
  change 7*w (2*456) + 5*(w (2*457)) - 5*w (2*456+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0912, w_guarded_leaf_0913, w_guarded_leaf_0914]
#print axioms pw_0912

/-- finite source-only pointWeight expansion at 913; no field reduction --/
lemma pw_0913 : pw 913 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gatherGather456, gather456]
  rw [hwe 456 (by omega), hwe 458 (by omega), hwo 456 (by omega), hwo 457 (by omega)]
  change -5*(w (2*456) - ((1073741824:M)*w (2*456) + (1073741824:M)*w (2*458))) + 7*w (2*456+1) + 5*(w (2*457+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0912, w_guarded_leaf_0913, w_guarded_leaf_0915, w_guarded_leaf_0916]
#print axioms pw_0913

/-- finite source-only pointWeight expansion at 914; no field reduction --/
lemma pw_0914 : pw 914 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather457]
  rw [hwe 456 (by omega), hwe 457 (by omega), hwe 458 (by omega), hwo 457 (by omega)]
  change 7*w (2*457) + 5*(((1073741824:M)^1)*w (2*456) + ((1073741824:M)^1)*w (2*458)) - 5*w (2*457+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0912, w_guarded_leaf_0914, w_guarded_leaf_0915, w_guarded_leaf_0916]
#print axioms pw_0914

/-- finite source-only pointWeight expansion at 916; no field reduction --/
lemma pw_0916 : pw 916 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather458]
  rw [hwe 458 (by omega), hwe 459 (by omega), hwo 458 (by omega)]
  change 7*w (2*458) + 5*(w (2*459)) - 5*w (2*458+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0916, w_guarded_leaf_0917, w_guarded_leaf_0918]
#print axioms pw_0916

/-- finite source-only pointWeight expansion at 917; no field reduction --/
lemma pw_0917 : pw 917 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gatherGather458, gather458]
  rw [hwe 456 (by omega), hwe 458 (by omega), hwe 460 (by omega), hwo 458 (by omega), hwo 459 (by omega)]
  change -5*(w (2*458) - ((1073741824:M)*w (2*458) + (1073741824:M)^2*w (2*456) + (1073741824:M)^2*w (2*460))) + 7*w (2*458+1) + 5*(w (2*459+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0912, w_guarded_leaf_0916, w_guarded_leaf_0917, w_guarded_leaf_0919, w_guarded_leaf_0920]
#print axioms pw_0917

/-- finite source-only pointWeight expansion at 918; no field reduction --/
lemma pw_0918 : pw 918 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather459]
  rw [hwe 456 (by omega), hwe 458 (by omega), hwe 459 (by omega), hwe 460 (by omega), hwo 459 (by omega)]
  change 7*w (2*459) + 5*(((1073741824:M)^1)*w (2*458) + ((1073741824:M)^2)*w (2*456) + ((1073741824:M)^2)*w (2*460)) - 5*w (2*459+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0912, w_guarded_leaf_0916, w_guarded_leaf_0918, w_guarded_leaf_0919, w_guarded_leaf_0920]
#print axioms pw_0918

/-- finite source-only pointWeight expansion at 920; no field reduction --/
lemma pw_0920 : pw 920 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather460]
  rw [hwe 460 (by omega), hwe 461 (by omega), hwo 460 (by omega)]
  change 7*w (2*460) + 5*(w (2*461)) - 5*w (2*460+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0920, w_guarded_leaf_0921, w_guarded_leaf_0922]
#print axioms pw_0920

/-- finite source-only pointWeight expansion at 921; no field reduction --/
lemma pw_0921 : pw 921 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gatherGather460, gather460]
  rw [hwe 460 (by omega), hwe 462 (by omega), hwo 460 (by omega), hwo 461 (by omega)]
  change -5*(w (2*460) - ((1073741824:M)*w (2*460) + (1073741824:M)*w (2*462))) + 7*w (2*460+1) + 5*(w (2*461+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0920, w_guarded_leaf_0921, w_guarded_leaf_0923, w_guarded_leaf_0924]
#print axioms pw_0921

/-- finite source-only pointWeight expansion at 922; no field reduction --/
lemma pw_0922 : pw 922 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather461]
  rw [hwe 460 (by omega), hwe 461 (by omega), hwe 462 (by omega), hwo 461 (by omega)]
  change 7*w (2*461) + 5*(((1073741824:M)^1)*w (2*460) + ((1073741824:M)^1)*w (2*462)) - 5*w (2*461+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0920, w_guarded_leaf_0922, w_guarded_leaf_0923, w_guarded_leaf_0924]
#print axioms pw_0922

/-- finite source-only pointWeight expansion at 924; no field reduction --/
lemma pw_0924 : pw 924 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather462]
  rw [hwe 462 (by omega), hwe 463 (by omega), hwo 462 (by omega)]
  change 7*w (2*462) + 5*(w (2*463)) - 5*w (2*462+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0924, w_guarded_leaf_0925, w_guarded_leaf_0926]
#print axioms pw_0924

/-- finite source-only pointWeight expansion at 925; no field reduction --/
lemma pw_0925 : pw 925 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((0 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^4*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gatherGather462, gather462]
  rw [hwe 448 (by omega), hwe 456 (by omega), hwe 460 (by omega), hwe 462 (by omega), hwe 464 (by omega), hwo 462 (by omega), hwo 463 (by omega)]
  change -5*(w (2*462) - ((1073741824:M)*w (2*462) + (1073741824:M)^2*w (2*460) + (1073741824:M)^3*w (2*456) + (1073741824:M)^4*w (2*448) + (1073741824:M)^4*w (2*464))) + 7*w (2*462+1) + 5*(w (2*463+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((0 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^4*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0896, w_guarded_leaf_0912, w_guarded_leaf_0920, w_guarded_leaf_0924, w_guarded_leaf_0925, w_guarded_leaf_0927, w_guarded_leaf_0928]
#print axioms pw_0925

/-- finite source-only pointWeight expansion at 926; no field reduction --/
lemma pw_0926 : pw 926 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^4)*((576 : M)) + ((1073741824:M)^4)*((0 : M))) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather463]
  rw [hwe 448 (by omega), hwe 456 (by omega), hwe 460 (by omega), hwe 462 (by omega), hwe 463 (by omega), hwe 464 (by omega), hwo 463 (by omega)]
  change 7*w (2*463) + 5*(((1073741824:M)^1)*w (2*462) + ((1073741824:M)^2)*w (2*460) + ((1073741824:M)^3)*w (2*456) + ((1073741824:M)^4)*w (2*448) + ((1073741824:M)^4)*w (2*464)) - 5*w (2*463+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^4)*((576 : M)) + ((1073741824:M)^4)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0896, w_guarded_leaf_0912, w_guarded_leaf_0920, w_guarded_leaf_0924, w_guarded_leaf_0926, w_guarded_leaf_0927, w_guarded_leaf_0928]
#print axioms pw_0926

/-- finite source-only pointWeight expansion at 928; no field reduction --/
lemma pw_0928 : pw 928 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather464]
  rw [hwe 464 (by omega), hwe 465 (by omega), hwo 464 (by omega)]
  change 7*w (2*464) + 5*(w (2*465)) - 5*w (2*464+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0928, w_guarded_leaf_0929, w_guarded_leaf_0930]
#print axioms pw_0928

/-- finite source-only pointWeight expansion at 929; no field reduction --/
lemma pw_0929 : pw 929 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gatherGather464, gather464]
  rw [hwe 464 (by omega), hwe 466 (by omega), hwo 464 (by omega), hwo 465 (by omega)]
  change -5*(w (2*464) - ((1073741824:M)*w (2*464) + (1073741824:M)*w (2*466))) + 7*w (2*464+1) + 5*(w (2*465+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0928, w_guarded_leaf_0929, w_guarded_leaf_0931, w_guarded_leaf_0932]
#print axioms pw_0929

/-- finite source-only pointWeight expansion at 930; no field reduction --/
lemma pw_0930 : pw 930 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather465]
  rw [hwe 464 (by omega), hwe 465 (by omega), hwe 466 (by omega), hwo 465 (by omega)]
  change 7*w (2*465) + 5*(((1073741824:M)^1)*w (2*464) + ((1073741824:M)^1)*w (2*466)) - 5*w (2*465+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0928, w_guarded_leaf_0930, w_guarded_leaf_0931, w_guarded_leaf_0932]
#print axioms pw_0930

/-- finite source-only pointWeight expansion at 932; no field reduction --/
lemma pw_0932 : pw 932 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather466]
  rw [hwe 466 (by omega), hwe 467 (by omega), hwo 466 (by omega)]
  change 7*w (2*466) + 5*(w (2*467)) - 5*w (2*466+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0932, w_guarded_leaf_0933, w_guarded_leaf_0934]
#print axioms pw_0932

/-- finite source-only pointWeight expansion at 933; no field reduction --/
lemma pw_0933 : pw 933 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gatherGather466, gather466]
  rw [hwe 464 (by omega), hwe 466 (by omega), hwe 468 (by omega), hwo 466 (by omega), hwo 467 (by omega)]
  change -5*(w (2*466) - ((1073741824:M)*w (2*466) + (1073741824:M)^2*w (2*464) + (1073741824:M)^2*w (2*468))) + 7*w (2*466+1) + 5*(w (2*467+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0928, w_guarded_leaf_0932, w_guarded_leaf_0933, w_guarded_leaf_0935, w_guarded_leaf_0936]
#print axioms pw_0933

/-- finite source-only pointWeight expansion at 934; no field reduction --/
lemma pw_0934 : pw 934 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather467]
  rw [hwe 464 (by omega), hwe 466 (by omega), hwe 467 (by omega), hwe 468 (by omega), hwo 467 (by omega)]
  change 7*w (2*467) + 5*(((1073741824:M)^1)*w (2*466) + ((1073741824:M)^2)*w (2*464) + ((1073741824:M)^2)*w (2*468)) - 5*w (2*467+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0928, w_guarded_leaf_0932, w_guarded_leaf_0934, w_guarded_leaf_0935, w_guarded_leaf_0936]
#print axioms pw_0934

/-- finite source-only pointWeight expansion at 936; no field reduction --/
lemma pw_0936 : pw 936 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather468]
  rw [hwe 468 (by omega), hwe 469 (by omega), hwo 468 (by omega)]
  change 7*w (2*468) + 5*(w (2*469)) - 5*w (2*468+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0936, w_guarded_leaf_0937, w_guarded_leaf_0938]
#print axioms pw_0936

/-- finite source-only pointWeight expansion at 937; no field reduction --/
lemma pw_0937 : pw 937 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gatherGather468, gather468]
  rw [hwe 468 (by omega), hwe 470 (by omega), hwo 468 (by omega), hwo 469 (by omega)]
  change -5*(w (2*468) - ((1073741824:M)*w (2*468) + (1073741824:M)*w (2*470))) + 7*w (2*468+1) + 5*(w (2*469+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0936, w_guarded_leaf_0937, w_guarded_leaf_0939, w_guarded_leaf_0940]
#print axioms pw_0937

/-- finite source-only pointWeight expansion at 938; no field reduction --/
lemma pw_0938 : pw 938 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather469]
  rw [hwe 468 (by omega), hwe 469 (by omega), hwe 470 (by omega), hwo 469 (by omega)]
  change 7*w (2*469) + 5*(((1073741824:M)^1)*w (2*468) + ((1073741824:M)^1)*w (2*470)) - 5*w (2*469+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0936, w_guarded_leaf_0938, w_guarded_leaf_0939, w_guarded_leaf_0940]
#print axioms pw_0938

/-- finite source-only pointWeight expansion at 940; no field reduction --/
lemma pw_0940 : pw 940 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather470]
  rw [hwe 470 (by omega), hwe 471 (by omega), hwo 470 (by omega)]
  change 7*w (2*470) + 5*(w (2*471)) - 5*w (2*470+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0940, w_guarded_leaf_0941, w_guarded_leaf_0942]
#print axioms pw_0940

/-- finite source-only pointWeight expansion at 941; no field reduction --/
lemma pw_0941 : pw 941 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((0 : M)) + (1073741824:M)^3*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gatherGather470, gather470]
  rw [hwe 464 (by omega), hwe 468 (by omega), hwe 470 (by omega), hwe 472 (by omega), hwo 470 (by omega), hwo 471 (by omega)]
  change -5*(w (2*470) - ((1073741824:M)*w (2*470) + (1073741824:M)^2*w (2*468) + (1073741824:M)^3*w (2*464) + (1073741824:M)^3*w (2*472))) + 7*w (2*470+1) + 5*(w (2*471+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((0 : M)) + (1073741824:M)^3*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0928, w_guarded_leaf_0936, w_guarded_leaf_0940, w_guarded_leaf_0941, w_guarded_leaf_0943, w_guarded_leaf_0944]
#print axioms pw_0941

/-- finite source-only pointWeight expansion at 942; no field reduction --/
lemma pw_0942 : pw 942 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^3)*((0 : M))) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather471]
  rw [hwe 464 (by omega), hwe 468 (by omega), hwe 470 (by omega), hwe 471 (by omega), hwe 472 (by omega), hwo 471 (by omega)]
  change 7*w (2*471) + 5*(((1073741824:M)^1)*w (2*470) + ((1073741824:M)^2)*w (2*468) + ((1073741824:M)^3)*w (2*464) + ((1073741824:M)^3)*w (2*472)) - 5*w (2*471+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^3)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0928, w_guarded_leaf_0936, w_guarded_leaf_0940, w_guarded_leaf_0942, w_guarded_leaf_0943, w_guarded_leaf_0944]
#print axioms pw_0942

/-- finite source-only pointWeight expansion at 944; no field reduction --/
lemma pw_0944 : pw 944 = 7*((0 : M)) + 5*((576 : M)) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather472]
  rw [hwe 472 (by omega), hwe 473 (by omega), hwo 472 (by omega)]
  change 7*w (2*472) + 5*(w (2*473)) - 5*w (2*472+1) = 7*((0 : M)) + 5*((576 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0944, w_guarded_leaf_0945, w_guarded_leaf_0946]
#print axioms pw_0944

/-- finite source-only pointWeight expansion at 945; no field reduction --/
lemma pw_0945 : pw 945 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gatherGather472, gather472]
  rw [hwe 472 (by omega), hwe 474 (by omega), hwo 472 (by omega), hwo 473 (by omega)]
  change -5*(w (2*472) - ((1073741824:M)*w (2*472) + (1073741824:M)*w (2*474))) + 7*w (2*472+1) + 5*(w (2*473+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0944, w_guarded_leaf_0945, w_guarded_leaf_0947, w_guarded_leaf_0948]
#print axioms pw_0945

/-- finite source-only pointWeight expansion at 948; no field reduction --/
lemma pw_0948 : pw 948 = 7*((0 : M)) + 5*((576 : M)) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather474]
  rw [hwe 474 (by omega), hwe 475 (by omega), hwo 474 (by omega)]
  change 7*w (2*474) + 5*(w (2*475)) - 5*w (2*474+1) = 7*((0 : M)) + 5*((576 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0948, w_guarded_leaf_0949, w_guarded_leaf_0950]
#print axioms pw_0948

/-- finite source-only pointWeight expansion at 949; no field reduction --/
lemma pw_0949 : pw 949 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gatherGather474, gather474]
  rw [hwe 472 (by omega), hwe 474 (by omega), hwe 476 (by omega), hwo 474 (by omega), hwo 475 (by omega)]
  change -5*(w (2*474) - ((1073741824:M)*w (2*474) + (1073741824:M)^2*w (2*472) + (1073741824:M)^2*w (2*476))) + 7*w (2*474+1) + 5*(w (2*475+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0944, w_guarded_leaf_0948, w_guarded_leaf_0949, w_guarded_leaf_0951, w_guarded_leaf_0952]
#print axioms pw_0949

/-- finite source-only pointWeight expansion at 952; no field reduction --/
lemma pw_0952 : pw 952 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
    unfold w
    rfl
  rw [gather476]
  rw [hwe 476 (by omega), hwe 477 (by omega), hwo 476 (by omega)]
  change 7*w (2*476) + 5*(w (2*477)) - 5*w (2*476+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0952, w_guarded_leaf_0953, w_guarded_leaf_0954]
#print axioms pw_0952

end
end AspisV8R19.R760PointWeightChunk08
