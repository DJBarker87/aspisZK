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

namespace AspisV8R19.R760PointWeightChunk02
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

/-- finite source-only pointWeight expansion at 184; no field reduction --/
lemma pw_0184 : pw 184 = 7*((0 : M)) + 5*((576:M)) - 5*((576:M)) := by
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
  rw [gather92]
  rw [hwe 92 (by omega), hwe 93 (by omega), hwo 92 (by omega)]
  change 7*w (2*92) + 5*(w (2*93)) - 5*w (2*92+1) = 7*((0 : M)) + 5*((576:M)) - 5*((576:M))
  rw [w_guarded_leaf_0184, w_185, w_186]
#print axioms pw_0184

/-- finite source-only pointWeight expansion at 185; no field reduction --/
lemma pw_0185 : pw 185 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((576:M)))) + 7*((576:M)) + 5*((576 : M)) := by
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
  rw [gatherGather92, gather92]
  rw [hwe 92 (by omega), hwe 94 (by omega), hwo 92 (by omega), hwo 93 (by omega)]
  change -5*(w (2*92) - ((1073741824:M)*w (2*92) + (1073741824:M)*w (2*94))) + 7*w (2*92+1) + 5*(w (2*93+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((576:M)))) + 7*((576:M)) + 5*((576 : M))
  rw [w_guarded_leaf_0184, w_185, w_guarded_leaf_0187, w_188]
#print axioms pw_0185

/-- finite source-only pointWeight expansion at 190; no field reduction --/
lemma pw_0190 : pw 190 = 7*((0:M)) + 5*(((1073741824:M)^1)*((576:M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^4)*((0 : M)) + ((1073741824:M)^5)*((0 : M)) + ((1073741824:M)^5)*((576 : M))) - 5*((576:M)) := by
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
  rw [gather95]
  rw [hwe 64 (by omega), hwe 80 (by omega), hwe 88 (by omega), hwe 92 (by omega), hwe 94 (by omega), hwe 95 (by omega), hwe 96 (by omega), hwo 95 (by omega)]
  change 7*w (2*95) + 5*(((1073741824:M)^1)*w (2*94) + ((1073741824:M)^2)*w (2*92) + ((1073741824:M)^3)*w (2*88) + ((1073741824:M)^4)*w (2*80) + ((1073741824:M)^5)*w (2*64) + ((1073741824:M)^5)*w (2*96)) - 5*w (2*95+1) = 7*((0:M)) + 5*(((1073741824:M)^1)*((576:M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^4)*((0 : M)) + ((1073741824:M)^5)*((0 : M)) + ((1073741824:M)^5)*((576 : M))) - 5*((576:M))
  rw [w_guarded_leaf_0128, w_guarded_leaf_0160, w_guarded_leaf_0176, w_guarded_leaf_0184, w_188, w_190, w_191, w_guarded_leaf_0192]
#print axioms pw_0190

/-- finite source-only pointWeight expansion at 192; no field reduction --/
lemma pw_0192 : pw 192 = 7*((576 : M)) + 5*((0:M)) - 5*((576:M)) := by
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
  rw [gather96]
  rw [hwe 96 (by omega), hwe 97 (by omega), hwo 96 (by omega)]
  change 7*w (2*96) + 5*(w (2*97)) - 5*w (2*96+1) = 7*((576 : M)) + 5*((0:M)) - 5*((576:M))
  rw [w_guarded_leaf_0192, w_193, w_194]
#print axioms pw_0192

/-- finite source-only pointWeight expansion at 194; no field reduction --/
lemma pw_0194 : pw 194 = 7*((0:M)) + 5*(((1073741824:M)^1)*((576 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather97]
  rw [hwe 96 (by omega), hwe 97 (by omega), hwe 98 (by omega), hwo 97 (by omega)]
  change 7*w (2*97) + 5*(((1073741824:M)^1)*w (2*96) + ((1073741824:M)^1)*w (2*98)) - 5*w (2*97+1) = 7*((0:M)) + 5*(((1073741824:M)^1)*((576 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0192, w_194, w_guarded_leaf_0195, w_guarded_leaf_0196]
#print axioms pw_0194

/-- finite source-only pointWeight expansion at 196; no field reduction --/
lemma pw_0196 : pw 196 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather98]
  rw [hwe 98 (by omega), hwe 99 (by omega), hwo 98 (by omega)]
  change 7*w (2*98) + 5*(w (2*99)) - 5*w (2*98+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0196, w_guarded_leaf_0197, w_guarded_leaf_0198]
#print axioms pw_0196

/-- finite source-only pointWeight expansion at 197; no field reduction --/
lemma pw_0197 : pw 197 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather98, gather98]
  rw [hwe 96 (by omega), hwe 98 (by omega), hwe 100 (by omega), hwo 98 (by omega), hwo 99 (by omega)]
  change -5*(w (2*98) - ((1073741824:M)*w (2*98) + (1073741824:M)^2*w (2*96) + (1073741824:M)^2*w (2*100))) + 7*w (2*98+1) + 5*(w (2*99+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0192, w_guarded_leaf_0196, w_guarded_leaf_0197, w_guarded_leaf_0199, w_guarded_leaf_0200]
#print axioms pw_0197

/-- finite source-only pointWeight expansion at 198; no field reduction --/
lemma pw_0198 : pw 198 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((576 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather99]
  rw [hwe 96 (by omega), hwe 98 (by omega), hwe 99 (by omega), hwe 100 (by omega), hwo 99 (by omega)]
  change 7*w (2*99) + 5*(((1073741824:M)^1)*w (2*98) + ((1073741824:M)^2)*w (2*96) + ((1073741824:M)^2)*w (2*100)) - 5*w (2*99+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((576 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0192, w_guarded_leaf_0196, w_guarded_leaf_0198, w_guarded_leaf_0199, w_guarded_leaf_0200]
#print axioms pw_0198

/-- finite source-only pointWeight expansion at 200; no field reduction --/
lemma pw_0200 : pw 200 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather100]
  rw [hwe 100 (by omega), hwe 101 (by omega), hwo 100 (by omega)]
  change 7*w (2*100) + 5*(w (2*101)) - 5*w (2*100+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0200, w_guarded_leaf_0201, w_guarded_leaf_0202]
#print axioms pw_0200

/-- finite source-only pointWeight expansion at 201; no field reduction --/
lemma pw_0201 : pw 201 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather100, gather100]
  rw [hwe 100 (by omega), hwe 102 (by omega), hwo 100 (by omega), hwo 101 (by omega)]
  change -5*(w (2*100) - ((1073741824:M)*w (2*100) + (1073741824:M)*w (2*102))) + 7*w (2*100+1) + 5*(w (2*101+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0200, w_guarded_leaf_0201, w_guarded_leaf_0203, w_guarded_leaf_0204]
#print axioms pw_0201

/-- finite source-only pointWeight expansion at 202; no field reduction --/
lemma pw_0202 : pw 202 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather101]
  rw [hwe 100 (by omega), hwe 101 (by omega), hwe 102 (by omega), hwo 101 (by omega)]
  change 7*w (2*101) + 5*(((1073741824:M)^1)*w (2*100) + ((1073741824:M)^1)*w (2*102)) - 5*w (2*101+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0200, w_guarded_leaf_0202, w_guarded_leaf_0203, w_guarded_leaf_0204]
#print axioms pw_0202

/-- finite source-only pointWeight expansion at 204; no field reduction --/
lemma pw_0204 : pw 204 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather102]
  rw [hwe 102 (by omega), hwe 103 (by omega), hwo 102 (by omega)]
  change 7*w (2*102) + 5*(w (2*103)) - 5*w (2*102+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0204, w_guarded_leaf_0205, w_guarded_leaf_0206]
#print axioms pw_0204

/-- finite source-only pointWeight expansion at 205; no field reduction --/
lemma pw_0205 : pw 205 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^3*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather102, gather102]
  rw [hwe 96 (by omega), hwe 100 (by omega), hwe 102 (by omega), hwe 104 (by omega), hwo 102 (by omega), hwo 103 (by omega)]
  change -5*(w (2*102) - ((1073741824:M)*w (2*102) + (1073741824:M)^2*w (2*100) + (1073741824:M)^3*w (2*96) + (1073741824:M)^3*w (2*104))) + 7*w (2*102+1) + 5*(w (2*103+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^3*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0192, w_guarded_leaf_0200, w_guarded_leaf_0204, w_guarded_leaf_0205, w_guarded_leaf_0207, w_guarded_leaf_0208]
#print axioms pw_0205

/-- finite source-only pointWeight expansion at 206; no field reduction --/
lemma pw_0206 : pw 206 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((576 : M)) + ((1073741824:M)^3)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather103]
  rw [hwe 96 (by omega), hwe 100 (by omega), hwe 102 (by omega), hwe 103 (by omega), hwe 104 (by omega), hwo 103 (by omega)]
  change 7*w (2*103) + 5*(((1073741824:M)^1)*w (2*102) + ((1073741824:M)^2)*w (2*100) + ((1073741824:M)^3)*w (2*96) + ((1073741824:M)^3)*w (2*104)) - 5*w (2*103+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((576 : M)) + ((1073741824:M)^3)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0192, w_guarded_leaf_0200, w_guarded_leaf_0204, w_guarded_leaf_0206, w_guarded_leaf_0207, w_guarded_leaf_0208]
#print axioms pw_0206

/-- finite source-only pointWeight expansion at 208; no field reduction --/
lemma pw_0208 : pw 208 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather104]
  rw [hwe 104 (by omega), hwe 105 (by omega), hwo 104 (by omega)]
  change 7*w (2*104) + 5*(w (2*105)) - 5*w (2*104+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0208, w_guarded_leaf_0209, w_guarded_leaf_0210]
#print axioms pw_0208

/-- finite source-only pointWeight expansion at 209; no field reduction --/
lemma pw_0209 : pw 209 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather104, gather104]
  rw [hwe 104 (by omega), hwe 106 (by omega), hwo 104 (by omega), hwo 105 (by omega)]
  change -5*(w (2*104) - ((1073741824:M)*w (2*104) + (1073741824:M)*w (2*106))) + 7*w (2*104+1) + 5*(w (2*105+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0208, w_guarded_leaf_0209, w_guarded_leaf_0211, w_guarded_leaf_0212]
#print axioms pw_0209

/-- finite source-only pointWeight expansion at 210; no field reduction --/
lemma pw_0210 : pw 210 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather105]
  rw [hwe 104 (by omega), hwe 105 (by omega), hwe 106 (by omega), hwo 105 (by omega)]
  change 7*w (2*105) + 5*(((1073741824:M)^1)*w (2*104) + ((1073741824:M)^1)*w (2*106)) - 5*w (2*105+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0208, w_guarded_leaf_0210, w_guarded_leaf_0211, w_guarded_leaf_0212]
#print axioms pw_0210

/-- finite source-only pointWeight expansion at 212; no field reduction --/
lemma pw_0212 : pw 212 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather106]
  rw [hwe 106 (by omega), hwe 107 (by omega), hwo 106 (by omega)]
  change 7*w (2*106) + 5*(w (2*107)) - 5*w (2*106+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0212, w_guarded_leaf_0213, w_guarded_leaf_0214]
#print axioms pw_0212

/-- finite source-only pointWeight expansion at 213; no field reduction --/
lemma pw_0213 : pw 213 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather106, gather106]
  rw [hwe 104 (by omega), hwe 106 (by omega), hwe 108 (by omega), hwo 106 (by omega), hwo 107 (by omega)]
  change -5*(w (2*106) - ((1073741824:M)*w (2*106) + (1073741824:M)^2*w (2*104) + (1073741824:M)^2*w (2*108))) + 7*w (2*106+1) + 5*(w (2*107+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0208, w_guarded_leaf_0212, w_guarded_leaf_0213, w_guarded_leaf_0215, w_guarded_leaf_0216]
#print axioms pw_0213

/-- finite source-only pointWeight expansion at 214; no field reduction --/
lemma pw_0214 : pw 214 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather107]
  rw [hwe 104 (by omega), hwe 106 (by omega), hwe 107 (by omega), hwe 108 (by omega), hwo 107 (by omega)]
  change 7*w (2*107) + 5*(((1073741824:M)^1)*w (2*106) + ((1073741824:M)^2)*w (2*104) + ((1073741824:M)^2)*w (2*108)) - 5*w (2*107+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0208, w_guarded_leaf_0212, w_guarded_leaf_0214, w_guarded_leaf_0215, w_guarded_leaf_0216]
#print axioms pw_0214

/-- finite source-only pointWeight expansion at 216; no field reduction --/
lemma pw_0216 : pw 216 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather108]
  rw [hwe 108 (by omega), hwe 109 (by omega), hwo 108 (by omega)]
  change 7*w (2*108) + 5*(w (2*109)) - 5*w (2*108+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0216, w_guarded_leaf_0217, w_guarded_leaf_0218]
#print axioms pw_0216

/-- finite source-only pointWeight expansion at 217; no field reduction --/
lemma pw_0217 : pw 217 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather108, gather108]
  rw [hwe 108 (by omega), hwe 110 (by omega), hwo 108 (by omega), hwo 109 (by omega)]
  change -5*(w (2*108) - ((1073741824:M)*w (2*108) + (1073741824:M)*w (2*110))) + 7*w (2*108+1) + 5*(w (2*109+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0216, w_guarded_leaf_0217, w_guarded_leaf_0219, w_guarded_leaf_0220]
#print axioms pw_0217

/-- finite source-only pointWeight expansion at 218; no field reduction --/
lemma pw_0218 : pw 218 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather109]
  rw [hwe 108 (by omega), hwe 109 (by omega), hwe 110 (by omega), hwo 109 (by omega)]
  change 7*w (2*109) + 5*(((1073741824:M)^1)*w (2*108) + ((1073741824:M)^1)*w (2*110)) - 5*w (2*109+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0216, w_guarded_leaf_0218, w_guarded_leaf_0219, w_guarded_leaf_0220]
#print axioms pw_0218

/-- finite source-only pointWeight expansion at 220; no field reduction --/
lemma pw_0220 : pw 220 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather110]
  rw [hwe 110 (by omega), hwe 111 (by omega), hwo 110 (by omega)]
  change 7*w (2*110) + 5*(w (2*111)) - 5*w (2*110+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0220, w_guarded_leaf_0221, w_guarded_leaf_0222]
#print axioms pw_0220

/-- finite source-only pointWeight expansion at 221; no field reduction --/
lemma pw_0221 : pw 221 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((0 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^4*((2147483575:M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather110, gather110]
  rw [hwe 96 (by omega), hwe 104 (by omega), hwe 108 (by omega), hwe 110 (by omega), hwe 112 (by omega), hwo 110 (by omega), hwo 111 (by omega)]
  change -5*(w (2*110) - ((1073741824:M)*w (2*110) + (1073741824:M)^2*w (2*108) + (1073741824:M)^3*w (2*104) + (1073741824:M)^4*w (2*96) + (1073741824:M)^4*w (2*112))) + 7*w (2*110+1) + 5*(w (2*111+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((0 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^4*((2147483575:M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0192, w_guarded_leaf_0208, w_guarded_leaf_0216, w_guarded_leaf_0220, w_guarded_leaf_0221, w_guarded_leaf_0223, transport_leaf_0224]
#print axioms pw_0221

/-- finite source-only pointWeight expansion at 222; no field reduction --/
lemma pw_0222 : pw 222 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^4)*((576 : M)) + ((1073741824:M)^4)*((2147483575:M))) - 5*((576 : M)) := by
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
  rw [gather111]
  rw [hwe 96 (by omega), hwe 104 (by omega), hwe 108 (by omega), hwe 110 (by omega), hwe 111 (by omega), hwe 112 (by omega), hwo 111 (by omega)]
  change 7*w (2*111) + 5*(((1073741824:M)^1)*w (2*110) + ((1073741824:M)^2)*w (2*108) + ((1073741824:M)^3)*w (2*104) + ((1073741824:M)^4)*w (2*96) + ((1073741824:M)^4)*w (2*112)) - 5*w (2*111+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^4)*((576 : M)) + ((1073741824:M)^4)*((2147483575:M))) - 5*((576 : M))
  rw [w_guarded_leaf_0192, w_guarded_leaf_0208, w_guarded_leaf_0216, w_guarded_leaf_0220, w_guarded_leaf_0222, w_guarded_leaf_0223, transport_leaf_0224]
#print axioms pw_0222

/-- finite source-only pointWeight expansion at 224; no field reduction --/
lemma pw_0224 : pw 224 = 7*((2147483575:M)) + 5*((144:M)) - 5*((36:M) + 576) := by
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
  rw [gather112]
  rw [hwe 112 (by omega), hwe 113 (by omega), hwo 112 (by omega)]
  change 7*w (2*112) + 5*(w (2*113)) - 5*w (2*112+1) = 7*((2147483575:M)) + 5*((144:M)) - 5*((36:M) + 576)
  rw [transport_leaf_0224, transport_leaf_0225, transport_leaf_0226]
#print axioms pw_0224

/-- finite source-only pointWeight expansion at 225; no field reduction --/
lemma pw_0225 : pw 225 = -5*(((2147483575:M)) - ((1073741824:M)*((2147483575:M)) + (1073741824:M)*((96:M)))) + 7*((36:M) + 576) + 5*((2147483575:M) + 576) := by
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
  rw [gatherGather112, gather112]
  rw [hwe 112 (by omega), hwe 114 (by omega), hwo 112 (by omega), hwo 113 (by omega)]
  change -5*(w (2*112) - ((1073741824:M)*w (2*112) + (1073741824:M)*w (2*114))) + 7*w (2*112+1) + 5*(w (2*113+1)) = -5*(((2147483575:M)) - ((1073741824:M)*((2147483575:M)) + (1073741824:M)*((96:M)))) + 7*((36:M) + 576) + 5*((2147483575:M) + 576)
  rw [transport_leaf_0224, transport_leaf_0225, transport_leaf_0227, transport_leaf_0228]
#print axioms pw_0225

/-- finite source-only pointWeight expansion at 226; no field reduction --/
lemma pw_0226 : pw 226 = 7*((144:M)) + 5*(((1073741824:M)^1)*((2147483575:M)) + ((1073741824:M)^1)*((96:M))) - 5*((2147483575:M) + 576) := by
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
  rw [gather113]
  rw [hwe 112 (by omega), hwe 113 (by omega), hwe 114 (by omega), hwo 113 (by omega)]
  change 7*w (2*113) + 5*(((1073741824:M)^1)*w (2*112) + ((1073741824:M)^1)*w (2*114)) - 5*w (2*113+1) = 7*((144:M)) + 5*(((1073741824:M)^1)*((2147483575:M)) + ((1073741824:M)^1)*((96:M))) - 5*((2147483575:M) + 576)
  rw [transport_leaf_0224, transport_leaf_0226, transport_leaf_0227, transport_leaf_0228]
#print axioms pw_0226

/-- finite source-only pointWeight expansion at 228; no field reduction --/
lemma pw_0228 : pw 228 = 7*((96:M)) + 5*((2147483455:M)) - 5*((2147483599:M) + 576) := by
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
  rw [gather114]
  rw [hwe 114 (by omega), hwe 115 (by omega), hwo 114 (by omega)]
  change 7*w (2*114) + 5*(w (2*115)) - 5*w (2*114+1) = 7*((96:M)) + 5*((2147483455:M)) - 5*((2147483599:M) + 576)
  rw [transport_leaf_0228, transport_leaf_0229, transport_leaf_0230]
#print axioms pw_0228

/-- finite source-only pointWeight expansion at 229; no field reduction --/
lemma pw_0229 : pw 229 = -5*(((96:M)) - ((1073741824:M)*((96:M)) + (1073741824:M)^2*((2147483575:M)) + (1073741824:M)^2*((108:M)))) + 7*((2147483599:M) + 576) + 5*((96:M) + 576) := by
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
  rw [gatherGather114, gather114]
  rw [hwe 112 (by omega), hwe 114 (by omega), hwe 116 (by omega), hwo 114 (by omega), hwo 115 (by omega)]
  change -5*(w (2*114) - ((1073741824:M)*w (2*114) + (1073741824:M)^2*w (2*112) + (1073741824:M)^2*w (2*116))) + 7*w (2*114+1) + 5*(w (2*115+1)) = -5*(((96:M)) - ((1073741824:M)*((96:M)) + (1073741824:M)^2*((2147483575:M)) + (1073741824:M)^2*((108:M)))) + 7*((2147483599:M) + 576) + 5*((96:M) + 576)
  rw [transport_leaf_0224, transport_leaf_0228, transport_leaf_0229, transport_leaf_0231, transport_leaf_0232]
#print axioms pw_0229

/-- finite source-only pointWeight expansion at 230; no field reduction --/
lemma pw_0230 : pw 230 = 7*((2147483455:M)) + 5*(((1073741824:M)^1)*((96:M)) + ((1073741824:M)^2)*((2147483575:M)) + ((1073741824:M)^2)*((108:M))) - 5*((96:M) + 576) := by
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
  rw [gather115]
  rw [hwe 112 (by omega), hwe 114 (by omega), hwe 115 (by omega), hwe 116 (by omega), hwo 115 (by omega)]
  change 7*w (2*115) + 5*(((1073741824:M)^1)*w (2*114) + ((1073741824:M)^2)*w (2*112) + ((1073741824:M)^2)*w (2*116)) - 5*w (2*115+1) = 7*((2147483455:M)) + 5*(((1073741824:M)^1)*((96:M)) + ((1073741824:M)^2)*((2147483575:M)) + ((1073741824:M)^2)*((108:M))) - 5*((96:M) + 576)
  rw [transport_leaf_0224, transport_leaf_0228, transport_leaf_0230, transport_leaf_0231, transport_leaf_0232]
#print axioms pw_0230

end
end AspisV8R19.R760PointWeightChunk02
