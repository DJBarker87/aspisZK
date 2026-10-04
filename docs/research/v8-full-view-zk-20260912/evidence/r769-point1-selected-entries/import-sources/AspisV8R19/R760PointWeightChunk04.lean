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

namespace AspisV8R19.R760PointWeightChunk04
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

/-- finite source-only pointWeight expansion at 276; no field reduction --/
lemma pw_0276 : pw 276 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather138]
  rw [hwe 138 (by omega), hwe 139 (by omega), hwo 138 (by omega)]
  change 7*w (2*138) + 5*(w (2*139)) - 5*w (2*138+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0276, w_guarded_leaf_0277, w_guarded_leaf_0278]
#print axioms pw_0276

/-- finite source-only pointWeight expansion at 277; no field reduction --/
lemma pw_0277 : pw 277 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather138, gather138]
  rw [hwe 136 (by omega), hwe 138 (by omega), hwe 140 (by omega), hwo 138 (by omega), hwo 139 (by omega)]
  change -5*(w (2*138) - ((1073741824:M)*w (2*138) + (1073741824:M)^2*w (2*136) + (1073741824:M)^2*w (2*140))) + 7*w (2*138+1) + 5*(w (2*139+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0272, w_guarded_leaf_0276, w_guarded_leaf_0277, w_guarded_leaf_0279, w_guarded_leaf_0280]
#print axioms pw_0277

/-- finite source-only pointWeight expansion at 279; no field reduction --/
lemma pw_0279 : pw 279 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) := by
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
  rw [gatherGather139, gather139]
  rw [hwe 137 (by omega), hwe 139 (by omega), hwe 141 (by omega), hwo 136 (by omega), hwo 138 (by omega), hwo 139 (by omega), hwo 140 (by omega)]
  change -5*(w (2*139) - ((1073741824:M)*w (2*139) + (1073741824:M)^2*w (2*137) + (1073741824:M)^2*w (2*141))) + 7*w (2*139+1) + 5*(((1073741824:M)^1)*w (2*138+1) + ((1073741824:M)^2)*w (2*136+1) + ((1073741824:M)^2)*w (2*140+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M)))
  rw [w_guarded_leaf_0273, w_guarded_leaf_0274, w_guarded_leaf_0277, w_guarded_leaf_0278, w_guarded_leaf_0279, w_guarded_leaf_0281, w_guarded_leaf_0282]
#print axioms pw_0279

/-- finite source-only pointWeight expansion at 280; no field reduction --/
lemma pw_0280 : pw 280 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather140]
  rw [hwe 140 (by omega), hwe 141 (by omega), hwo 140 (by omega)]
  change 7*w (2*140) + 5*(w (2*141)) - 5*w (2*140+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0280, w_guarded_leaf_0281, w_guarded_leaf_0282]
#print axioms pw_0280

/-- finite source-only pointWeight expansion at 281; no field reduction --/
lemma pw_0281 : pw 281 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather140, gather140]
  rw [hwe 140 (by omega), hwe 142 (by omega), hwo 140 (by omega), hwo 141 (by omega)]
  change -5*(w (2*140) - ((1073741824:M)*w (2*140) + (1073741824:M)*w (2*142))) + 7*w (2*140+1) + 5*(w (2*141+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0280, w_guarded_leaf_0281, w_guarded_leaf_0283, w_guarded_leaf_0284]
#print axioms pw_0281

/-- finite source-only pointWeight expansion at 283; no field reduction --/
lemma pw_0283 : pw 283 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) := by
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
  rw [gatherGather141, gather141]
  rw [hwe 141 (by omega), hwe 143 (by omega), hwo 140 (by omega), hwo 141 (by omega), hwo 142 (by omega)]
  change -5*(w (2*141) - ((1073741824:M)*w (2*141) + (1073741824:M)*w (2*143))) + 7*w (2*141+1) + 5*(((1073741824:M)^1)*w (2*140+1) + ((1073741824:M)^1)*w (2*142+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M)))
  rw [w_guarded_leaf_0281, w_guarded_leaf_0282, w_guarded_leaf_0283, w_guarded_leaf_0285, w_guarded_leaf_0286]
#print axioms pw_0283

/-- finite source-only pointWeight expansion at 284; no field reduction --/
lemma pw_0284 : pw 284 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather142]
  rw [hwe 142 (by omega), hwe 143 (by omega), hwo 142 (by omega)]
  change 7*w (2*142) + 5*(w (2*143)) - 5*w (2*142+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0284, w_guarded_leaf_0285, w_guarded_leaf_0286]
#print axioms pw_0284

/-- finite source-only pointWeight expansion at 285; no field reduction --/
lemma pw_0285 : pw 285 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^4*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather142, gather142]
  rw [hwe 128 (by omega), hwe 136 (by omega), hwe 140 (by omega), hwe 142 (by omega), hwe 144 (by omega), hwo 142 (by omega), hwo 143 (by omega)]
  change -5*(w (2*142) - ((1073741824:M)*w (2*142) + (1073741824:M)^2*w (2*140) + (1073741824:M)^3*w (2*136) + (1073741824:M)^4*w (2*128) + (1073741824:M)^4*w (2*144))) + 7*w (2*142+1) + 5*(w (2*143+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^4*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0256, w_guarded_leaf_0272, w_guarded_leaf_0280, w_guarded_leaf_0284, w_guarded_leaf_0285, w_guarded_leaf_0287, w_guarded_leaf_0288]
#print axioms pw_0285

/-- finite source-only pointWeight expansion at 287; no field reduction --/
lemma pw_0287 : pw 287 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^4*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^4)*((0 : M)) + ((1073741824:M)^4)*((0 : M))) := by
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
  rw [gatherGather143, gather143]
  rw [hwe 129 (by omega), hwe 137 (by omega), hwe 141 (by omega), hwe 143 (by omega), hwe 145 (by omega), hwo 128 (by omega), hwo 136 (by omega), hwo 140 (by omega), hwo 142 (by omega), hwo 143 (by omega), hwo 144 (by omega)]
  change -5*(w (2*143) - ((1073741824:M)*w (2*143) + (1073741824:M)^2*w (2*141) + (1073741824:M)^3*w (2*137) + (1073741824:M)^4*w (2*129) + (1073741824:M)^4*w (2*145))) + 7*w (2*143+1) + 5*(((1073741824:M)^1)*w (2*142+1) + ((1073741824:M)^2)*w (2*140+1) + ((1073741824:M)^3)*w (2*136+1) + ((1073741824:M)^4)*w (2*128+1) + ((1073741824:M)^4)*w (2*144+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^4*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^4)*((0 : M)) + ((1073741824:M)^4)*((0 : M)))
  rw [w_guarded_leaf_0257, w_guarded_leaf_0258, w_guarded_leaf_0273, w_guarded_leaf_0274, w_guarded_leaf_0281, w_guarded_leaf_0282, w_guarded_leaf_0285, w_guarded_leaf_0286, w_guarded_leaf_0287, w_guarded_leaf_0289, w_guarded_leaf_0290]
#print axioms pw_0287

/-- finite source-only pointWeight expansion at 288; no field reduction --/
lemma pw_0288 : pw 288 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather144]
  rw [hwe 144 (by omega), hwe 145 (by omega), hwo 144 (by omega)]
  change 7*w (2*144) + 5*(w (2*145)) - 5*w (2*144+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0288, w_guarded_leaf_0289, w_guarded_leaf_0290]
#print axioms pw_0288

/-- finite source-only pointWeight expansion at 289; no field reduction --/
lemma pw_0289 : pw 289 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather144, gather144]
  rw [hwe 144 (by omega), hwe 146 (by omega), hwo 144 (by omega), hwo 145 (by omega)]
  change -5*(w (2*144) - ((1073741824:M)*w (2*144) + (1073741824:M)*w (2*146))) + 7*w (2*144+1) + 5*(w (2*145+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0288, w_guarded_leaf_0289, w_guarded_leaf_0291, w_guarded_leaf_0292]
#print axioms pw_0289

/-- finite source-only pointWeight expansion at 291; no field reduction --/
lemma pw_0291 : pw 291 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) := by
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
  rw [gatherGather145, gather145]
  rw [hwe 145 (by omega), hwe 147 (by omega), hwo 144 (by omega), hwo 145 (by omega), hwo 146 (by omega)]
  change -5*(w (2*145) - ((1073741824:M)*w (2*145) + (1073741824:M)*w (2*147))) + 7*w (2*145+1) + 5*(((1073741824:M)^1)*w (2*144+1) + ((1073741824:M)^1)*w (2*146+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M)))
  rw [w_guarded_leaf_0289, w_guarded_leaf_0290, w_guarded_leaf_0291, w_guarded_leaf_0293, w_guarded_leaf_0294]
#print axioms pw_0291

/-- finite source-only pointWeight expansion at 292; no field reduction --/
lemma pw_0292 : pw 292 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather146]
  rw [hwe 146 (by omega), hwe 147 (by omega), hwo 146 (by omega)]
  change 7*w (2*146) + 5*(w (2*147)) - 5*w (2*146+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0292, w_guarded_leaf_0293, w_guarded_leaf_0294]
#print axioms pw_0292

/-- finite source-only pointWeight expansion at 293; no field reduction --/
lemma pw_0293 : pw 293 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather146, gather146]
  rw [hwe 144 (by omega), hwe 146 (by omega), hwe 148 (by omega), hwo 146 (by omega), hwo 147 (by omega)]
  change -5*(w (2*146) - ((1073741824:M)*w (2*146) + (1073741824:M)^2*w (2*144) + (1073741824:M)^2*w (2*148))) + 7*w (2*146+1) + 5*(w (2*147+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0288, w_guarded_leaf_0292, w_guarded_leaf_0293, w_guarded_leaf_0295, w_guarded_leaf_0296]
#print axioms pw_0293

/-- finite source-only pointWeight expansion at 295; no field reduction --/
lemma pw_0295 : pw 295 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) := by
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
  rw [gatherGather147, gather147]
  rw [hwe 145 (by omega), hwe 147 (by omega), hwe 149 (by omega), hwo 144 (by omega), hwo 146 (by omega), hwo 147 (by omega), hwo 148 (by omega)]
  change -5*(w (2*147) - ((1073741824:M)*w (2*147) + (1073741824:M)^2*w (2*145) + (1073741824:M)^2*w (2*149))) + 7*w (2*147+1) + 5*(((1073741824:M)^1)*w (2*146+1) + ((1073741824:M)^2)*w (2*144+1) + ((1073741824:M)^2)*w (2*148+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M)))
  rw [w_guarded_leaf_0289, w_guarded_leaf_0290, w_guarded_leaf_0293, w_guarded_leaf_0294, w_guarded_leaf_0295, w_guarded_leaf_0297, w_guarded_leaf_0298]
#print axioms pw_0295

/-- finite source-only pointWeight expansion at 296; no field reduction --/
lemma pw_0296 : pw 296 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather148]
  rw [hwe 148 (by omega), hwe 149 (by omega), hwo 148 (by omega)]
  change 7*w (2*148) + 5*(w (2*149)) - 5*w (2*148+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0296, w_guarded_leaf_0297, w_guarded_leaf_0298]
#print axioms pw_0296

/-- finite source-only pointWeight expansion at 297; no field reduction --/
lemma pw_0297 : pw 297 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather148, gather148]
  rw [hwe 148 (by omega), hwe 150 (by omega), hwo 148 (by omega), hwo 149 (by omega)]
  change -5*(w (2*148) - ((1073741824:M)*w (2*148) + (1073741824:M)*w (2*150))) + 7*w (2*148+1) + 5*(w (2*149+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0296, w_guarded_leaf_0297, w_guarded_leaf_0299, w_guarded_leaf_0300]
#print axioms pw_0297

/-- finite source-only pointWeight expansion at 299; no field reduction --/
lemma pw_0299 : pw 299 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) := by
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
  rw [gatherGather149, gather149]
  rw [hwe 149 (by omega), hwe 151 (by omega), hwo 148 (by omega), hwo 149 (by omega), hwo 150 (by omega)]
  change -5*(w (2*149) - ((1073741824:M)*w (2*149) + (1073741824:M)*w (2*151))) + 7*w (2*149+1) + 5*(((1073741824:M)^1)*w (2*148+1) + ((1073741824:M)^1)*w (2*150+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M)))
  rw [w_guarded_leaf_0297, w_guarded_leaf_0298, w_guarded_leaf_0299, w_guarded_leaf_0301, w_guarded_leaf_0302]
#print axioms pw_0299

/-- finite source-only pointWeight expansion at 300; no field reduction --/
lemma pw_0300 : pw 300 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather150]
  rw [hwe 150 (by omega), hwe 151 (by omega), hwo 150 (by omega)]
  change 7*w (2*150) + 5*(w (2*151)) - 5*w (2*150+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0300, w_guarded_leaf_0301, w_guarded_leaf_0302]
#print axioms pw_0300

/-- finite source-only pointWeight expansion at 301; no field reduction --/
lemma pw_0301 : pw 301 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^3*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather150, gather150]
  rw [hwe 144 (by omega), hwe 148 (by omega), hwe 150 (by omega), hwe 152 (by omega), hwo 150 (by omega), hwo 151 (by omega)]
  change -5*(w (2*150) - ((1073741824:M)*w (2*150) + (1073741824:M)^2*w (2*148) + (1073741824:M)^3*w (2*144) + (1073741824:M)^3*w (2*152))) + 7*w (2*150+1) + 5*(w (2*151+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^3*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0288, w_guarded_leaf_0296, w_guarded_leaf_0300, w_guarded_leaf_0301, w_guarded_leaf_0303, w_guarded_leaf_0304]
#print axioms pw_0301

/-- finite source-only pointWeight expansion at 303; no field reduction --/
lemma pw_0303 : pw 303 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^3*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^3)*((0 : M))) := by
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
  rw [gatherGather151, gather151]
  rw [hwe 145 (by omega), hwe 149 (by omega), hwe 151 (by omega), hwe 153 (by omega), hwo 144 (by omega), hwo 148 (by omega), hwo 150 (by omega), hwo 151 (by omega), hwo 152 (by omega)]
  change -5*(w (2*151) - ((1073741824:M)*w (2*151) + (1073741824:M)^2*w (2*149) + (1073741824:M)^3*w (2*145) + (1073741824:M)^3*w (2*153))) + 7*w (2*151+1) + 5*(((1073741824:M)^1)*w (2*150+1) + ((1073741824:M)^2)*w (2*148+1) + ((1073741824:M)^3)*w (2*144+1) + ((1073741824:M)^3)*w (2*152+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^3*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^3)*((0 : M)))
  rw [w_guarded_leaf_0289, w_guarded_leaf_0290, w_guarded_leaf_0297, w_guarded_leaf_0298, w_guarded_leaf_0301, w_guarded_leaf_0302, w_guarded_leaf_0303, w_guarded_leaf_0305, w_guarded_leaf_0306]
#print axioms pw_0303

/-- finite source-only pointWeight expansion at 304; no field reduction --/
lemma pw_0304 : pw 304 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather152]
  rw [hwe 152 (by omega), hwe 153 (by omega), hwo 152 (by omega)]
  change 7*w (2*152) + 5*(w (2*153)) - 5*w (2*152+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0304, w_guarded_leaf_0305, w_guarded_leaf_0306]
#print axioms pw_0304

/-- finite source-only pointWeight expansion at 305; no field reduction --/
lemma pw_0305 : pw 305 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather152, gather152]
  rw [hwe 152 (by omega), hwe 154 (by omega), hwo 152 (by omega), hwo 153 (by omega)]
  change -5*(w (2*152) - ((1073741824:M)*w (2*152) + (1073741824:M)*w (2*154))) + 7*w (2*152+1) + 5*(w (2*153+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0304, w_guarded_leaf_0305, w_guarded_leaf_0307, w_guarded_leaf_0308]
#print axioms pw_0305

/-- finite source-only pointWeight expansion at 307; no field reduction --/
lemma pw_0307 : pw 307 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((576 : M))) := by
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
  rw [gatherGather153, gather153]
  rw [hwe 153 (by omega), hwe 155 (by omega), hwo 152 (by omega), hwo 153 (by omega), hwo 154 (by omega)]
  change -5*(w (2*153) - ((1073741824:M)*w (2*153) + (1073741824:M)*w (2*155))) + 7*w (2*153+1) + 5*(((1073741824:M)^1)*w (2*152+1) + ((1073741824:M)^1)*w (2*154+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((576 : M)))
  rw [w_guarded_leaf_0305, w_guarded_leaf_0306, w_guarded_leaf_0307, w_guarded_leaf_0309, w_guarded_leaf_0310]
#print axioms pw_0307

/-- finite source-only pointWeight expansion at 308; no field reduction --/
lemma pw_0308 : pw 308 = 7*((576 : M)) + 5*((576 : M)) - 5*((576 : M)) := by
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
  rw [gather154]
  rw [hwe 154 (by omega), hwe 155 (by omega), hwo 154 (by omega)]
  change 7*w (2*154) + 5*(w (2*155)) - 5*w (2*154+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0308, w_guarded_leaf_0309, w_guarded_leaf_0310]
#print axioms pw_0308

/-- finite source-only pointWeight expansion at 311; no field reduction --/
lemma pw_0311 : pw 311 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((576 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) := by
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
  rw [gatherGather155, gather155]
  rw [hwe 153 (by omega), hwe 155 (by omega), hwe 157 (by omega), hwo 152 (by omega), hwo 154 (by omega), hwo 155 (by omega), hwo 156 (by omega)]
  change -5*(w (2*155) - ((1073741824:M)*w (2*155) + (1073741824:M)^2*w (2*153) + (1073741824:M)^2*w (2*157))) + 7*w (2*155+1) + 5*(((1073741824:M)^1)*w (2*154+1) + ((1073741824:M)^2)*w (2*152+1) + ((1073741824:M)^2)*w (2*156+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((576 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M)))
  rw [w_guarded_leaf_0305, w_guarded_leaf_0306, w_guarded_leaf_0309, w_guarded_leaf_0310, w_guarded_leaf_0311, w_guarded_leaf_0313, w_guarded_leaf_0314]
#print axioms pw_0311

/-- finite source-only pointWeight expansion at 312; no field reduction --/
lemma pw_0312 : pw 312 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather156]
  rw [hwe 156 (by omega), hwe 157 (by omega), hwo 156 (by omega)]
  change 7*w (2*156) + 5*(w (2*157)) - 5*w (2*156+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0312, w_guarded_leaf_0313, w_guarded_leaf_0314]
#print axioms pw_0312

/-- finite source-only pointWeight expansion at 313; no field reduction --/
lemma pw_0313 : pw 313 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather156, gather156]
  rw [hwe 156 (by omega), hwe 158 (by omega), hwo 156 (by omega), hwo 157 (by omega)]
  change -5*(w (2*156) - ((1073741824:M)*w (2*156) + (1073741824:M)*w (2*158))) + 7*w (2*156+1) + 5*(w (2*157+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0312, w_guarded_leaf_0313, w_guarded_leaf_0315, w_guarded_leaf_0316]
#print axioms pw_0313

/-- finite source-only pointWeight expansion at 315; no field reduction --/
lemma pw_0315 : pw 315 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) := by
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
  rw [gatherGather157, gather157]
  rw [hwe 157 (by omega), hwe 159 (by omega), hwo 156 (by omega), hwo 157 (by omega), hwo 158 (by omega)]
  change -5*(w (2*157) - ((1073741824:M)*w (2*157) + (1073741824:M)*w (2*159))) + 7*w (2*157+1) + 5*(((1073741824:M)^1)*w (2*156+1) + ((1073741824:M)^1)*w (2*158+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M)))
  rw [w_guarded_leaf_0313, w_guarded_leaf_0314, w_guarded_leaf_0315, w_guarded_leaf_0317, w_guarded_leaf_0318]
#print axioms pw_0315

/-- finite source-only pointWeight expansion at 316; no field reduction --/
lemma pw_0316 : pw 316 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather158]
  rw [hwe 158 (by omega), hwe 159 (by omega), hwo 158 (by omega)]
  change 7*w (2*158) + 5*(w (2*159)) - 5*w (2*158+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0316, w_guarded_leaf_0317, w_guarded_leaf_0318]
#print axioms pw_0316

/-- finite source-only pointWeight expansion at 317; no field reduction --/
lemma pw_0317 : pw 317 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^5*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather158, gather158]
  rw [hwe 128 (by omega), hwe 144 (by omega), hwe 152 (by omega), hwe 156 (by omega), hwe 158 (by omega), hwe 160 (by omega), hwo 158 (by omega), hwo 159 (by omega)]
  change -5*(w (2*158) - ((1073741824:M)*w (2*158) + (1073741824:M)^2*w (2*156) + (1073741824:M)^3*w (2*152) + (1073741824:M)^4*w (2*144) + (1073741824:M)^5*w (2*128) + (1073741824:M)^5*w (2*160))) + 7*w (2*158+1) + 5*(w (2*159+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^5*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0256, w_guarded_leaf_0288, w_guarded_leaf_0304, w_guarded_leaf_0312, w_guarded_leaf_0316, w_guarded_leaf_0317, w_guarded_leaf_0319, w_guarded_leaf_0320]
#print axioms pw_0317

/-- finite source-only pointWeight expansion at 319; no field reduction --/
lemma pw_0319 : pw 319 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^5*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^4)*((0 : M)) + ((1073741824:M)^5)*((0 : M)) + ((1073741824:M)^5)*((0 : M))) := by
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
  rw [gatherGather159, gather159]
  rw [hwe 129 (by omega), hwe 145 (by omega), hwe 153 (by omega), hwe 157 (by omega), hwe 159 (by omega), hwe 161 (by omega), hwo 128 (by omega), hwo 144 (by omega), hwo 152 (by omega), hwo 156 (by omega), hwo 158 (by omega), hwo 159 (by omega), hwo 160 (by omega)]
  change -5*(w (2*159) - ((1073741824:M)*w (2*159) + (1073741824:M)^2*w (2*157) + (1073741824:M)^3*w (2*153) + (1073741824:M)^4*w (2*145) + (1073741824:M)^5*w (2*129) + (1073741824:M)^5*w (2*161))) + 7*w (2*159+1) + 5*(((1073741824:M)^1)*w (2*158+1) + ((1073741824:M)^2)*w (2*156+1) + ((1073741824:M)^3)*w (2*152+1) + ((1073741824:M)^4)*w (2*144+1) + ((1073741824:M)^5)*w (2*128+1) + ((1073741824:M)^5)*w (2*160+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^5*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^4)*((0 : M)) + ((1073741824:M)^5)*((0 : M)) + ((1073741824:M)^5)*((0 : M)))
  rw [w_guarded_leaf_0257, w_guarded_leaf_0258, w_guarded_leaf_0289, w_guarded_leaf_0290, w_guarded_leaf_0305, w_guarded_leaf_0306, w_guarded_leaf_0313, w_guarded_leaf_0314, w_guarded_leaf_0317, w_guarded_leaf_0318, w_guarded_leaf_0319, w_guarded_leaf_0321, w_guarded_leaf_0322]
#print axioms pw_0319

end
end AspisV8R19.R760PointWeightChunk04
