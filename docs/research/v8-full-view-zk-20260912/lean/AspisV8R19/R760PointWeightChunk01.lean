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

namespace AspisV8R19.R760PointWeightChunk01
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

/-- finite source-only pointWeight expansion at 140; no field reduction --/
lemma pw_0140 : pw 140 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather70]
  rw [hwe 70 (by omega), hwe 71 (by omega), hwo 70 (by omega)]
  change 7*w (2*70) + 5*(w (2*71)) - 5*w (2*70+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0140, w_guarded_leaf_0141, w_guarded_leaf_0142]
#print axioms pw_0140

/-- finite source-only pointWeight expansion at 141; no field reduction --/
lemma pw_0141 : pw 141 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((0 : M)) + (1073741824:M)^3*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather70, gather70]
  rw [hwe 64 (by omega), hwe 68 (by omega), hwe 70 (by omega), hwe 72 (by omega), hwo 70 (by omega), hwo 71 (by omega)]
  change -5*(w (2*70) - ((1073741824:M)*w (2*70) + (1073741824:M)^2*w (2*68) + (1073741824:M)^3*w (2*64) + (1073741824:M)^3*w (2*72))) + 7*w (2*70+1) + 5*(w (2*71+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((0 : M)) + (1073741824:M)^3*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0128, w_guarded_leaf_0136, w_guarded_leaf_0140, w_guarded_leaf_0141, w_guarded_leaf_0143, w_guarded_leaf_0144]
#print axioms pw_0141

/-- finite source-only pointWeight expansion at 142; no field reduction --/
lemma pw_0142 : pw 142 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^3)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather71]
  rw [hwe 64 (by omega), hwe 68 (by omega), hwe 70 (by omega), hwe 71 (by omega), hwe 72 (by omega), hwo 71 (by omega)]
  change 7*w (2*71) + 5*(((1073741824:M)^1)*w (2*70) + ((1073741824:M)^2)*w (2*68) + ((1073741824:M)^3)*w (2*64) + ((1073741824:M)^3)*w (2*72)) - 5*w (2*71+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^3)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0128, w_guarded_leaf_0136, w_guarded_leaf_0140, w_guarded_leaf_0142, w_guarded_leaf_0143, w_guarded_leaf_0144]
#print axioms pw_0142

/-- finite source-only pointWeight expansion at 144; no field reduction --/
lemma pw_0144 : pw 144 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather72]
  rw [hwe 72 (by omega), hwe 73 (by omega), hwo 72 (by omega)]
  change 7*w (2*72) + 5*(w (2*73)) - 5*w (2*72+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0144, w_guarded_leaf_0145, w_guarded_leaf_0146]
#print axioms pw_0144

/-- finite source-only pointWeight expansion at 145; no field reduction --/
lemma pw_0145 : pw 145 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather72, gather72]
  rw [hwe 72 (by omega), hwe 74 (by omega), hwo 72 (by omega), hwo 73 (by omega)]
  change -5*(w (2*72) - ((1073741824:M)*w (2*72) + (1073741824:M)*w (2*74))) + 7*w (2*72+1) + 5*(w (2*73+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0144, w_guarded_leaf_0145, w_guarded_leaf_0147, w_guarded_leaf_0148]
#print axioms pw_0145

/-- finite source-only pointWeight expansion at 146; no field reduction --/
lemma pw_0146 : pw 146 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather73]
  rw [hwe 72 (by omega), hwe 73 (by omega), hwe 74 (by omega), hwo 73 (by omega)]
  change 7*w (2*73) + 5*(((1073741824:M)^1)*w (2*72) + ((1073741824:M)^1)*w (2*74)) - 5*w (2*73+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0144, w_guarded_leaf_0146, w_guarded_leaf_0147, w_guarded_leaf_0148]
#print axioms pw_0146

/-- finite source-only pointWeight expansion at 148; no field reduction --/
lemma pw_0148 : pw 148 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather74]
  rw [hwe 74 (by omega), hwe 75 (by omega), hwo 74 (by omega)]
  change 7*w (2*74) + 5*(w (2*75)) - 5*w (2*74+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0148, w_guarded_leaf_0149, w_guarded_leaf_0150]
#print axioms pw_0148

/-- finite source-only pointWeight expansion at 149; no field reduction --/
lemma pw_0149 : pw 149 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather74, gather74]
  rw [hwe 72 (by omega), hwe 74 (by omega), hwe 76 (by omega), hwo 74 (by omega), hwo 75 (by omega)]
  change -5*(w (2*74) - ((1073741824:M)*w (2*74) + (1073741824:M)^2*w (2*72) + (1073741824:M)^2*w (2*76))) + 7*w (2*74+1) + 5*(w (2*75+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0144, w_guarded_leaf_0148, w_guarded_leaf_0149, w_guarded_leaf_0151, w_guarded_leaf_0152]
#print axioms pw_0149

/-- finite source-only pointWeight expansion at 150; no field reduction --/
lemma pw_0150 : pw 150 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather75]
  rw [hwe 72 (by omega), hwe 74 (by omega), hwe 75 (by omega), hwe 76 (by omega), hwo 75 (by omega)]
  change 7*w (2*75) + 5*(((1073741824:M)^1)*w (2*74) + ((1073741824:M)^2)*w (2*72) + ((1073741824:M)^2)*w (2*76)) - 5*w (2*75+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0144, w_guarded_leaf_0148, w_guarded_leaf_0150, w_guarded_leaf_0151, w_guarded_leaf_0152]
#print axioms pw_0150

/-- finite source-only pointWeight expansion at 152; no field reduction --/
lemma pw_0152 : pw 152 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather76]
  rw [hwe 76 (by omega), hwe 77 (by omega), hwo 76 (by omega)]
  change 7*w (2*76) + 5*(w (2*77)) - 5*w (2*76+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0152, w_guarded_leaf_0153, w_guarded_leaf_0154]
#print axioms pw_0152

/-- finite source-only pointWeight expansion at 153; no field reduction --/
lemma pw_0153 : pw 153 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather76, gather76]
  rw [hwe 76 (by omega), hwe 78 (by omega), hwo 76 (by omega), hwo 77 (by omega)]
  change -5*(w (2*76) - ((1073741824:M)*w (2*76) + (1073741824:M)*w (2*78))) + 7*w (2*76+1) + 5*(w (2*77+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0152, w_guarded_leaf_0153, w_guarded_leaf_0155, w_guarded_leaf_0156]
#print axioms pw_0153

/-- finite source-only pointWeight expansion at 154; no field reduction --/
lemma pw_0154 : pw 154 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather77]
  rw [hwe 76 (by omega), hwe 77 (by omega), hwe 78 (by omega), hwo 77 (by omega)]
  change 7*w (2*77) + 5*(((1073741824:M)^1)*w (2*76) + ((1073741824:M)^1)*w (2*78)) - 5*w (2*77+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0152, w_guarded_leaf_0154, w_guarded_leaf_0155, w_guarded_leaf_0156]
#print axioms pw_0154

/-- finite source-only pointWeight expansion at 156; no field reduction --/
lemma pw_0156 : pw 156 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather78]
  rw [hwe 78 (by omega), hwe 79 (by omega), hwo 78 (by omega)]
  change 7*w (2*78) + 5*(w (2*79)) - 5*w (2*78+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0156, w_guarded_leaf_0157, w_guarded_leaf_0158]
#print axioms pw_0156

/-- finite source-only pointWeight expansion at 157; no field reduction --/
lemma pw_0157 : pw 157 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((0 : M)) + (1073741824:M)^4*((0 : M)) + (1073741824:M)^4*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather78, gather78]
  rw [hwe 64 (by omega), hwe 72 (by omega), hwe 76 (by omega), hwe 78 (by omega), hwe 80 (by omega), hwo 78 (by omega), hwo 79 (by omega)]
  change -5*(w (2*78) - ((1073741824:M)*w (2*78) + (1073741824:M)^2*w (2*76) + (1073741824:M)^3*w (2*72) + (1073741824:M)^4*w (2*64) + (1073741824:M)^4*w (2*80))) + 7*w (2*78+1) + 5*(w (2*79+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((0 : M)) + (1073741824:M)^4*((0 : M)) + (1073741824:M)^4*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0128, w_guarded_leaf_0144, w_guarded_leaf_0152, w_guarded_leaf_0156, w_guarded_leaf_0157, w_guarded_leaf_0159, w_guarded_leaf_0160]
#print axioms pw_0157

/-- finite source-only pointWeight expansion at 158; no field reduction --/
lemma pw_0158 : pw 158 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^4)*((0 : M)) + ((1073741824:M)^4)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather79]
  rw [hwe 64 (by omega), hwe 72 (by omega), hwe 76 (by omega), hwe 78 (by omega), hwe 79 (by omega), hwe 80 (by omega), hwo 79 (by omega)]
  change 7*w (2*79) + 5*(((1073741824:M)^1)*w (2*78) + ((1073741824:M)^2)*w (2*76) + ((1073741824:M)^3)*w (2*72) + ((1073741824:M)^4)*w (2*64) + ((1073741824:M)^4)*w (2*80)) - 5*w (2*79+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^4)*((0 : M)) + ((1073741824:M)^4)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0128, w_guarded_leaf_0144, w_guarded_leaf_0152, w_guarded_leaf_0156, w_guarded_leaf_0158, w_guarded_leaf_0159, w_guarded_leaf_0160]
#print axioms pw_0158

/-- finite source-only pointWeight expansion at 160; no field reduction --/
lemma pw_0160 : pw 160 = 7*((0 : M)) + 5*((0:M)) - 5*((576:M)) := by
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
  rw [gather80]
  rw [hwe 80 (by omega), hwe 81 (by omega), hwo 80 (by omega)]
  change 7*w (2*80) + 5*(w (2*81)) - 5*w (2*80+1) = 7*((0 : M)) + 5*((0:M)) - 5*((576:M))
  rw [w_guarded_leaf_0160, w_161, w_162]
#print axioms pw_0160

/-- finite source-only pointWeight expansion at 161; no field reduction --/
lemma pw_0161 : pw 161 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576:M)) + 5*((576 : M)) := by
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
  rw [gatherGather80, gather80]
  rw [hwe 80 (by omega), hwe 82 (by omega), hwo 80 (by omega), hwo 81 (by omega)]
  change -5*(w (2*80) - ((1073741824:M)*w (2*80) + (1073741824:M)*w (2*82))) + 7*w (2*80+1) + 5*(w (2*81+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576:M)) + 5*((576 : M))
  rw [w_guarded_leaf_0160, w_161, w_guarded_leaf_0163, w_guarded_leaf_0164]
#print axioms pw_0161

/-- finite source-only pointWeight expansion at 162; no field reduction --/
lemma pw_0162 : pw 162 = 7*((0:M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather81]
  rw [hwe 80 (by omega), hwe 81 (by omega), hwe 82 (by omega), hwo 81 (by omega)]
  change 7*w (2*81) + 5*(((1073741824:M)^1)*w (2*80) + ((1073741824:M)^1)*w (2*82)) - 5*w (2*81+1) = 7*((0:M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0160, w_162, w_guarded_leaf_0163, w_guarded_leaf_0164]
#print axioms pw_0162

/-- finite source-only pointWeight expansion at 164; no field reduction --/
lemma pw_0164 : pw 164 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather82]
  rw [hwe 82 (by omega), hwe 83 (by omega), hwo 82 (by omega)]
  change 7*w (2*82) + 5*(w (2*83)) - 5*w (2*82+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0164, w_guarded_leaf_0165, w_guarded_leaf_0166]
#print axioms pw_0164

/-- finite source-only pointWeight expansion at 165; no field reduction --/
lemma pw_0165 : pw 165 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather82, gather82]
  rw [hwe 80 (by omega), hwe 82 (by omega), hwe 84 (by omega), hwo 82 (by omega), hwo 83 (by omega)]
  change -5*(w (2*82) - ((1073741824:M)*w (2*82) + (1073741824:M)^2*w (2*80) + (1073741824:M)^2*w (2*84))) + 7*w (2*82+1) + 5*(w (2*83+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0160, w_guarded_leaf_0164, w_guarded_leaf_0165, w_guarded_leaf_0167, w_guarded_leaf_0168]
#print axioms pw_0165

/-- finite source-only pointWeight expansion at 166; no field reduction --/
lemma pw_0166 : pw 166 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather83]
  rw [hwe 80 (by omega), hwe 82 (by omega), hwe 83 (by omega), hwe 84 (by omega), hwo 83 (by omega)]
  change 7*w (2*83) + 5*(((1073741824:M)^1)*w (2*82) + ((1073741824:M)^2)*w (2*80) + ((1073741824:M)^2)*w (2*84)) - 5*w (2*83+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0160, w_guarded_leaf_0164, w_guarded_leaf_0166, w_guarded_leaf_0167, w_guarded_leaf_0168]
#print axioms pw_0166

/-- finite source-only pointWeight expansion at 168; no field reduction --/
lemma pw_0168 : pw 168 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather84]
  rw [hwe 84 (by omega), hwe 85 (by omega), hwo 84 (by omega)]
  change 7*w (2*84) + 5*(w (2*85)) - 5*w (2*84+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0168, w_guarded_leaf_0169, w_guarded_leaf_0170]
#print axioms pw_0168

/-- finite source-only pointWeight expansion at 169; no field reduction --/
lemma pw_0169 : pw 169 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather84, gather84]
  rw [hwe 84 (by omega), hwe 86 (by omega), hwo 84 (by omega), hwo 85 (by omega)]
  change -5*(w (2*84) - ((1073741824:M)*w (2*84) + (1073741824:M)*w (2*86))) + 7*w (2*84+1) + 5*(w (2*85+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0168, w_guarded_leaf_0169, w_guarded_leaf_0171, w_guarded_leaf_0172]
#print axioms pw_0169

/-- finite source-only pointWeight expansion at 170; no field reduction --/
lemma pw_0170 : pw 170 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather85]
  rw [hwe 84 (by omega), hwe 85 (by omega), hwe 86 (by omega), hwo 85 (by omega)]
  change 7*w (2*85) + 5*(((1073741824:M)^1)*w (2*84) + ((1073741824:M)^1)*w (2*86)) - 5*w (2*85+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0168, w_guarded_leaf_0170, w_guarded_leaf_0171, w_guarded_leaf_0172]
#print axioms pw_0170

/-- finite source-only pointWeight expansion at 172; no field reduction --/
lemma pw_0172 : pw 172 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather86]
  rw [hwe 86 (by omega), hwe 87 (by omega), hwo 86 (by omega)]
  change 7*w (2*86) + 5*(w (2*87)) - 5*w (2*86+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0172, w_guarded_leaf_0173, w_guarded_leaf_0174]
#print axioms pw_0172

/-- finite source-only pointWeight expansion at 173; no field reduction --/
lemma pw_0173 : pw 173 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((0 : M)) + (1073741824:M)^3*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather86, gather86]
  rw [hwe 80 (by omega), hwe 84 (by omega), hwe 86 (by omega), hwe 88 (by omega), hwo 86 (by omega), hwo 87 (by omega)]
  change -5*(w (2*86) - ((1073741824:M)*w (2*86) + (1073741824:M)^2*w (2*84) + (1073741824:M)^3*w (2*80) + (1073741824:M)^3*w (2*88))) + 7*w (2*86+1) + 5*(w (2*87+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((0 : M)) + (1073741824:M)^3*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0160, w_guarded_leaf_0168, w_guarded_leaf_0172, w_guarded_leaf_0173, w_guarded_leaf_0175, w_guarded_leaf_0176]
#print axioms pw_0173

/-- finite source-only pointWeight expansion at 174; no field reduction --/
lemma pw_0174 : pw 174 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^3)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather87]
  rw [hwe 80 (by omega), hwe 84 (by omega), hwe 86 (by omega), hwe 87 (by omega), hwe 88 (by omega), hwo 87 (by omega)]
  change 7*w (2*87) + 5*(((1073741824:M)^1)*w (2*86) + ((1073741824:M)^2)*w (2*84) + ((1073741824:M)^3)*w (2*80) + ((1073741824:M)^3)*w (2*88)) - 5*w (2*87+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^3)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0160, w_guarded_leaf_0168, w_guarded_leaf_0172, w_guarded_leaf_0174, w_guarded_leaf_0175, w_guarded_leaf_0176]
#print axioms pw_0174

/-- finite source-only pointWeight expansion at 176; no field reduction --/
lemma pw_0176 : pw 176 = 7*((0 : M)) + 5*((0:M)) - 5*((576:M)) := by
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
  rw [gather88]
  rw [hwe 88 (by omega), hwe 89 (by omega), hwo 88 (by omega)]
  change 7*w (2*88) + 5*(w (2*89)) - 5*w (2*88+1) = 7*((0 : M)) + 5*((0:M)) - 5*((576:M))
  rw [w_guarded_leaf_0176, w_177, w_178]
#print axioms pw_0176

/-- finite source-only pointWeight expansion at 177; no field reduction --/
lemma pw_0177 : pw 177 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576:M)) + 5*((576 : M)) := by
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
  rw [gatherGather88, gather88]
  rw [hwe 88 (by omega), hwe 90 (by omega), hwo 88 (by omega), hwo 89 (by omega)]
  change -5*(w (2*88) - ((1073741824:M)*w (2*88) + (1073741824:M)*w (2*90))) + 7*w (2*88+1) + 5*(w (2*89+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576:M)) + 5*((576 : M))
  rw [w_guarded_leaf_0176, w_177, w_guarded_leaf_0179, w_guarded_leaf_0180]
#print axioms pw_0177

/-- finite source-only pointWeight expansion at 178; no field reduction --/
lemma pw_0178 : pw 178 = 7*((0:M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather89]
  rw [hwe 88 (by omega), hwe 89 (by omega), hwe 90 (by omega), hwo 89 (by omega)]
  change 7*w (2*89) + 5*(((1073741824:M)^1)*w (2*88) + ((1073741824:M)^1)*w (2*90)) - 5*w (2*89+1) = 7*((0:M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0176, w_178, w_guarded_leaf_0179, w_guarded_leaf_0180]
#print axioms pw_0178

/-- finite source-only pointWeight expansion at 180; no field reduction --/
lemma pw_0180 : pw 180 = 7*((0 : M)) + 5*((576 : M)) - 5*((576 : M)) := by
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
  rw [gather90]
  rw [hwe 90 (by omega), hwe 91 (by omega), hwo 90 (by omega)]
  change 7*w (2*90) + 5*(w (2*91)) - 5*w (2*90+1) = 7*((0 : M)) + 5*((576 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0180, w_guarded_leaf_0181, w_guarded_leaf_0182]
#print axioms pw_0180

/-- finite source-only pointWeight expansion at 181; no field reduction --/
lemma pw_0181 : pw 181 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather90, gather90]
  rw [hwe 88 (by omega), hwe 90 (by omega), hwe 92 (by omega), hwo 90 (by omega), hwo 91 (by omega)]
  change -5*(w (2*90) - ((1073741824:M)*w (2*90) + (1073741824:M)^2*w (2*88) + (1073741824:M)^2*w (2*92))) + 7*w (2*90+1) + 5*(w (2*91+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0176, w_guarded_leaf_0180, w_guarded_leaf_0181, w_guarded_leaf_0183, w_guarded_leaf_0184]
#print axioms pw_0181

end
end AspisV8R19.R760PointWeightChunk01
