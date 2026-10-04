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

namespace AspisV8R19.R760PointWeightChunk06
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

/-- finite source-only pointWeight expansion at 364; no field reduction --/
lemma pw_0364 : pw 364 = 7*((2147483455:M) + 576) + 5*((384:M) + 576) - 5*((96:M)) := by
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
  rw [gather182]
  rw [hwe 182 (by omega), hwe 183 (by omega), hwo 182 (by omega)]
  change 7*w (2*182) + 5*(w (2*183)) - 5*w (2*182+1) = 7*((2147483455:M) + 576) + 5*((384:M) + 576) - 5*((96:M))
  rw [transport_leaf_0364, transport_leaf_0365, transport_leaf_0366]
#print axioms pw_0364

/-- finite source-only pointWeight expansion at 365; no field reduction --/
lemma pw_0365 : pw 365 = -5*(((2147483455:M) + 576) - ((1073741824:M)*((2147483455:M) + 576) + (1073741824:M)^2*((144:M) + 576) + (1073741824:M)^3*((2147483551:M) + 576) + (1073741824:M)^3*((192:M) + 576))) + 7*((96:M)) + 5*((2147483455:M)) := by
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
  rw [gatherGather182, gather182]
  rw [hwe 176 (by omega), hwe 180 (by omega), hwe 182 (by omega), hwe 184 (by omega), hwo 182 (by omega), hwo 183 (by omega)]
  change -5*(w (2*182) - ((1073741824:M)*w (2*182) + (1073741824:M)^2*w (2*180) + (1073741824:M)^3*w (2*176) + (1073741824:M)^3*w (2*184))) + 7*w (2*182+1) + 5*(w (2*183+1)) = -5*(((2147483455:M) + 576) - ((1073741824:M)*((2147483455:M) + 576) + (1073741824:M)^2*((144:M) + 576) + (1073741824:M)^3*((2147483551:M) + 576) + (1073741824:M)^3*((192:M) + 576))) + 7*((96:M)) + 5*((2147483455:M))
  rw [transport_leaf_0352, transport_leaf_0360, transport_leaf_0364, transport_leaf_0365, transport_leaf_0367, transport_leaf_0368]
#print axioms pw_0365

/-- finite source-only pointWeight expansion at 367; no field reduction --/
lemma pw_0367 : pw 367 = -5*(((384:M) + 576) - ((1073741824:M)*((384:M) + 576) + (1073741824:M)^2*((2147483359:M) + 576) + (1073741824:M)^3*((192:M) + 576) + (1073741824:M)^3*((2147483263:M)))) + 7*((2147483455:M)) + 5*(((1073741824:M)^1)*((96:M)) + ((1073741824:M)^2)*((2147483575:M)) + ((1073741824:M)^3)*((48:M)) + ((1073741824:M)^3)*((2147483551:M) + 576)) := by
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
  rw [gatherGather183, gather183]
  rw [hwe 177 (by omega), hwe 181 (by omega), hwe 183 (by omega), hwe 185 (by omega), hwo 176 (by omega), hwo 180 (by omega), hwo 182 (by omega), hwo 183 (by omega), hwo 184 (by omega)]
  change -5*(w (2*183) - ((1073741824:M)*w (2*183) + (1073741824:M)^2*w (2*181) + (1073741824:M)^3*w (2*177) + (1073741824:M)^3*w (2*185))) + 7*w (2*183+1) + 5*(((1073741824:M)^1)*w (2*182+1) + ((1073741824:M)^2)*w (2*180+1) + ((1073741824:M)^3)*w (2*176+1) + ((1073741824:M)^3)*w (2*184+1)) = -5*(((384:M) + 576) - ((1073741824:M)*((384:M) + 576) + (1073741824:M)^2*((2147483359:M) + 576) + (1073741824:M)^3*((192:M) + 576) + (1073741824:M)^3*((2147483263:M)))) + 7*((2147483455:M)) + 5*(((1073741824:M)^1)*((96:M)) + ((1073741824:M)^2)*((2147483575:M)) + ((1073741824:M)^3)*((48:M)) + ((1073741824:M)^3)*((2147483551:M) + 576))
  rw [transport_leaf_0353, transport_leaf_0354, transport_leaf_0361, transport_leaf_0362, transport_leaf_0365, transport_leaf_0366, transport_leaf_0367, transport_leaf_0369, transport_leaf_0370]
#print axioms pw_0367

/-- finite source-only pointWeight expansion at 368; no field reduction --/
lemma pw_0368 : pw 368 = 7*((192:M) + 576) + 5*((2147483263:M)) - 5*((2147483551:M) + 576) := by
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
  rw [gather184]
  rw [hwe 184 (by omega), hwe 185 (by omega), hwo 184 (by omega)]
  change 7*w (2*184) + 5*(w (2*185)) - 5*w (2*184+1) = 7*((192:M) + 576) + 5*((2147483263:M)) - 5*((2147483551:M) + 576)
  rw [transport_leaf_0368, transport_leaf_0369, transport_leaf_0370]
#print axioms pw_0368

/-- finite source-only pointWeight expansion at 370; no field reduction --/
lemma pw_0370 : pw 370 = 7*((2147483263:M)) + 5*(((1073741824:M)^1)*((192:M) + 576) + ((1073741824:M)^1)*((2147483391:M))) - 5*((192:M) + 576) := by
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
  rw [gather185]
  rw [hwe 184 (by omega), hwe 185 (by omega), hwe 186 (by omega), hwo 185 (by omega)]
  change 7*w (2*185) + 5*(((1073741824:M)^1)*w (2*184) + ((1073741824:M)^1)*w (2*186)) - 5*w (2*185+1) = 7*((2147483263:M)) + 5*(((1073741824:M)^1)*((192:M) + 576) + ((1073741824:M)^1)*((2147483391:M))) - 5*((192:M) + 576)
  rw [transport_leaf_0368, transport_leaf_0370, transport_leaf_0371, transport_leaf_0372]
#print axioms pw_0370

/-- finite source-only pointWeight expansion at 372; no field reduction --/
lemma pw_0372 : pw 372 = 7*((2147483391:M)) + 5*((512:M)) - 5*((128:M) + 576) := by
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
  rw [gather186]
  rw [hwe 186 (by omega), hwe 187 (by omega), hwo 186 (by omega)]
  change 7*w (2*186) + 5*(w (2*187)) - 5*w (2*186+1) = 7*((2147483391:M)) + 5*((512:M)) - 5*((128:M) + 576)
  rw [transport_leaf_0372, transport_leaf_0373, transport_leaf_0374]
#print axioms pw_0372

/-- finite source-only pointWeight expansion at 373; no field reduction --/
lemma pw_0373 : pw 373 = -5*(((2147483391:M)) - ((1073741824:M)*((2147483391:M)) + (1073741824:M)^2*((192:M) + 576) + (1073741824:M)^2*((2147483359:M)))) + 7*((128:M) + 576) + 5*((2147483391:M) + 576) := by
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
  rw [gatherGather186, gather186]
  rw [hwe 184 (by omega), hwe 186 (by omega), hwe 188 (by omega), hwo 186 (by omega), hwo 187 (by omega)]
  change -5*(w (2*186) - ((1073741824:M)*w (2*186) + (1073741824:M)^2*w (2*184) + (1073741824:M)^2*w (2*188))) + 7*w (2*186+1) + 5*(w (2*187+1)) = -5*(((2147483391:M)) - ((1073741824:M)*((2147483391:M)) + (1073741824:M)^2*((192:M) + 576) + (1073741824:M)^2*((2147483359:M)))) + 7*((128:M) + 576) + 5*((2147483391:M) + 576)
  rw [transport_leaf_0368, transport_leaf_0372, transport_leaf_0373, transport_leaf_0375, transport_leaf_0376]
#print axioms pw_0373

/-- finite source-only pointWeight expansion at 374; no field reduction --/
lemma pw_0374 : pw 374 = 7*((512:M)) + 5*(((1073741824:M)^1)*((2147483391:M)) + ((1073741824:M)^2)*((192:M) + 576) + ((1073741824:M)^2)*((2147483359:M))) - 5*((2147483391:M) + 576) := by
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
  rw [gather187]
  rw [hwe 184 (by omega), hwe 186 (by omega), hwe 187 (by omega), hwe 188 (by omega), hwo 187 (by omega)]
  change 7*w (2*187) + 5*(((1073741824:M)^1)*w (2*186) + ((1073741824:M)^2)*w (2*184) + ((1073741824:M)^2)*w (2*188)) - 5*w (2*187+1) = 7*((512:M)) + 5*(((1073741824:M)^1)*((2147483391:M)) + ((1073741824:M)^2)*((192:M) + 576) + ((1073741824:M)^2)*((2147483359:M))) - 5*((2147483391:M) + 576)
  rw [transport_leaf_0368, transport_leaf_0372, transport_leaf_0374, transport_leaf_0375, transport_leaf_0376]
#print axioms pw_0374

/-- finite source-only pointWeight expansion at 376; no field reduction --/
lemma pw_0376 : pw 376 = 7*((2147483359:M)) + 5*((576:M)) - 5*((144:M) + 576) := by
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
  rw [gather188]
  rw [hwe 188 (by omega), hwe 189 (by omega), hwo 188 (by omega)]
  change 7*w (2*188) + 5*(w (2*189)) - 5*w (2*188+1) = 7*((2147483359:M)) + 5*((576:M)) - 5*((144:M) + 576)
  rw [transport_leaf_0376, transport_leaf_0377, transport_leaf_0378]
#print axioms pw_0376

/-- finite source-only pointWeight expansion at 377; no field reduction --/
lemma pw_0377 : pw 377 = -5*(((2147483359:M)) - ((1073741824:M)*((2147483359:M)) + (1073741824:M)*((384:M)))) + 7*((144:M) + 576) + 5*((2147483359:M) + 576) := by
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
  rw [gatherGather188, gather188]
  rw [hwe 188 (by omega), hwe 190 (by omega), hwo 188 (by omega), hwo 189 (by omega)]
  change -5*(w (2*188) - ((1073741824:M)*w (2*188) + (1073741824:M)*w (2*190))) + 7*w (2*188+1) + 5*(w (2*189+1)) = -5*(((2147483359:M)) - ((1073741824:M)*((2147483359:M)) + (1073741824:M)*((384:M)))) + 7*((144:M) + 576) + 5*((2147483359:M) + 576)
  rw [transport_leaf_0376, transport_leaf_0377, transport_leaf_0379, transport_leaf_0380]
#print axioms pw_0377

/-- finite source-only pointWeight expansion at 378; no field reduction --/
lemma pw_0378 : pw 378 = 7*((576:M)) + 5*(((1073741824:M)^1)*((2147483359:M)) + ((1073741824:M)^1)*((384:M))) - 5*((2147483359:M) + 576) := by
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
  rw [gather189]
  rw [hwe 188 (by omega), hwe 189 (by omega), hwe 190 (by omega), hwo 189 (by omega)]
  change 7*w (2*189) + 5*(((1073741824:M)^1)*w (2*188) + ((1073741824:M)^1)*w (2*190)) - 5*w (2*189+1) = 7*((576:M)) + 5*(((1073741824:M)^1)*((2147483359:M)) + ((1073741824:M)^1)*((384:M))) - 5*((2147483359:M) + 576)
  rw [transport_leaf_0376, transport_leaf_0378, transport_leaf_0379, transport_leaf_0380]
#print axioms pw_0378

/-- finite source-only pointWeight expansion at 380; no field reduction --/
lemma pw_0380 : pw 380 = 7*((384:M)) + 5*((2147482879:M)) - 5*((2147483455:M) + 576) := by
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
  rw [gather190]
  rw [hwe 190 (by omega), hwe 191 (by omega), hwo 190 (by omega)]
  change 7*w (2*190) + 5*(w (2*191)) - 5*w (2*190+1) = 7*((384:M)) + 5*((2147482879:M)) - 5*((2147483455:M) + 576)
  rw [transport_leaf_0380, transport_leaf_0381, transport_leaf_0382]
#print axioms pw_0380

/-- finite source-only pointWeight expansion at 381; no field reduction --/
lemma pw_0381 : pw 381 = -5*(((384:M)) - ((1073741824:M)*((384:M)) + (1073741824:M)^2*((2147483359:M)) + (1073741824:M)^3*((192:M) + 576) + (1073741824:M)^4*((2147483551:M) + 576) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^6*((576 : M)) + (1073741824:M)^6*((576 : M)))) + 7*((2147483455:M) + 576) + 5*((384:M) + 576) := by
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
  rw [gatherGather190, gather190]
  rw [hwe 128 (by omega), hwe 160 (by omega), hwe 176 (by omega), hwe 184 (by omega), hwe 188 (by omega), hwe 190 (by omega), hwe 192 (by omega), hwo 190 (by omega), hwo 191 (by omega)]
  change -5*(w (2*190) - ((1073741824:M)*w (2*190) + (1073741824:M)^2*w (2*188) + (1073741824:M)^3*w (2*184) + (1073741824:M)^4*w (2*176) + (1073741824:M)^5*w (2*160) + (1073741824:M)^6*w (2*128) + (1073741824:M)^6*w (2*192))) + 7*w (2*190+1) + 5*(w (2*191+1)) = -5*(((384:M)) - ((1073741824:M)*((384:M)) + (1073741824:M)^2*((2147483359:M)) + (1073741824:M)^3*((192:M) + 576) + (1073741824:M)^4*((2147483551:M) + 576) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^6*((576 : M)) + (1073741824:M)^6*((576 : M)))) + 7*((2147483455:M) + 576) + 5*((384:M) + 576)
  rw [w_guarded_leaf_0256, w_guarded_leaf_0320, transport_leaf_0352, transport_leaf_0368, transport_leaf_0376, transport_leaf_0380, transport_leaf_0381, transport_leaf_0383, w_guarded_leaf_0384]
#print axioms pw_0381

/-- finite source-only pointWeight expansion at 382; no field reduction --/
lemma pw_0382 : pw 382 = 7*((2147482879:M)) + 5*(((1073741824:M)^1)*((384:M)) + ((1073741824:M)^2)*((2147483359:M)) + ((1073741824:M)^3)*((192:M) + 576) + ((1073741824:M)^4)*((2147483551:M) + 576) + ((1073741824:M)^5)*((576 : M)) + ((1073741824:M)^6)*((576 : M)) + ((1073741824:M)^6)*((576 : M))) - 5*((384:M) + 576) := by
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
  rw [gather191]
  rw [hwe 128 (by omega), hwe 160 (by omega), hwe 176 (by omega), hwe 184 (by omega), hwe 188 (by omega), hwe 190 (by omega), hwe 191 (by omega), hwe 192 (by omega), hwo 191 (by omega)]
  change 7*w (2*191) + 5*(((1073741824:M)^1)*w (2*190) + ((1073741824:M)^2)*w (2*188) + ((1073741824:M)^3)*w (2*184) + ((1073741824:M)^4)*w (2*176) + ((1073741824:M)^5)*w (2*160) + ((1073741824:M)^6)*w (2*128) + ((1073741824:M)^6)*w (2*192)) - 5*w (2*191+1) = 7*((2147482879:M)) + 5*(((1073741824:M)^1)*((384:M)) + ((1073741824:M)^2)*((2147483359:M)) + ((1073741824:M)^3)*((192:M) + 576) + ((1073741824:M)^4)*((2147483551:M) + 576) + ((1073741824:M)^5)*((576 : M)) + ((1073741824:M)^6)*((576 : M)) + ((1073741824:M)^6)*((576 : M))) - 5*((384:M) + 576)
  rw [w_guarded_leaf_0256, w_guarded_leaf_0320, transport_leaf_0352, transport_leaf_0368, transport_leaf_0376, transport_leaf_0380, transport_leaf_0382, transport_leaf_0383, w_guarded_leaf_0384]
#print axioms pw_0382

/-- finite source-only pointWeight expansion at 496; no field reduction --/
lemma pw_0496 : pw 496 = 7*((2147483551:M) + 576) + 5*((192:M) + 576) - 5*((48:M) + 576) := by
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
  rw [gather248]
  rw [hwe 248 (by omega), hwe 249 (by omega), hwo 248 (by omega)]
  change 7*w (2*248) + 5*(w (2*249)) - 5*w (2*248+1) = 7*((2147483551:M) + 576) + 5*((192:M) + 576) - 5*((48:M) + 576)
  rw [transport_leaf_0496, transport_leaf_0497, transport_leaf_0498]
#print axioms pw_0496

/-- finite source-only pointWeight expansion at 499; no field reduction --/
lemma pw_0499 : pw 499 = -5*(((192:M) + 576) - ((1073741824:M)*((192:M) + 576) + (1073741824:M)*((2147483391:M) + 576))) + 7*((2147483551:M)) + 5*(((1073741824:M)^1)*((48:M) + 576) + ((1073741824:M)^1)*((2147483583:M))) := by
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
  rw [gatherGather249, gather249]
  rw [hwe 249 (by omega), hwe 251 (by omega), hwo 248 (by omega), hwo 249 (by omega), hwo 250 (by omega)]
  change -5*(w (2*249) - ((1073741824:M)*w (2*249) + (1073741824:M)*w (2*251))) + 7*w (2*249+1) + 5*(((1073741824:M)^1)*w (2*248+1) + ((1073741824:M)^1)*w (2*250+1)) = -5*(((192:M) + 576) - ((1073741824:M)*((192:M) + 576) + (1073741824:M)*((2147483391:M) + 576))) + 7*((2147483551:M)) + 5*(((1073741824:M)^1)*((48:M) + 576) + ((1073741824:M)^1)*((2147483583:M)))
  rw [transport_leaf_0497, transport_leaf_0498, transport_leaf_0499, transport_leaf_0501, transport_leaf_0502]
#print axioms pw_0499

/-- finite source-only pointWeight expansion at 500; no field reduction --/
lemma pw_0500 : pw 500 = 7*((128:M) + 576) + 5*((2147483391:M) + 576) - 5*((2147483583:M)) := by
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
  rw [gather250]
  rw [hwe 250 (by omega), hwe 251 (by omega), hwo 250 (by omega)]
  change 7*w (2*250) + 5*(w (2*251)) - 5*w (2*250+1) = 7*((128:M) + 576) + 5*((2147483391:M) + 576) - 5*((2147483583:M))
  rw [transport_leaf_0500, transport_leaf_0501, transport_leaf_0502]
#print axioms pw_0500

/-- finite source-only pointWeight expansion at 501; no field reduction --/
lemma pw_0501 : pw 501 = -5*(((128:M) + 576) - ((1073741824:M)*((128:M) + 576) + (1073741824:M)^2*((2147483551:M) + 576) + (1073741824:M)^2*((144:M) + 576))) + 7*((2147483583:M)) + 5*((128:M)) := by
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
  rw [gatherGather250, gather250]
  rw [hwe 248 (by omega), hwe 250 (by omega), hwe 252 (by omega), hwo 250 (by omega), hwo 251 (by omega)]
  change -5*(w (2*250) - ((1073741824:M)*w (2*250) + (1073741824:M)^2*w (2*248) + (1073741824:M)^2*w (2*252))) + 7*w (2*250+1) + 5*(w (2*251+1)) = -5*(((128:M) + 576) - ((1073741824:M)*((128:M) + 576) + (1073741824:M)^2*((2147483551:M) + 576) + (1073741824:M)^2*((144:M) + 576))) + 7*((2147483583:M)) + 5*((128:M))
  rw [transport_leaf_0496, transport_leaf_0500, transport_leaf_0501, transport_leaf_0503, transport_leaf_0504]
#print axioms pw_0501

/-- finite source-only pointWeight expansion at 503; no field reduction --/
lemma pw_0503 : pw 503 = -5*(((2147483391:M) + 576) - ((1073741824:M)*((2147483391:M) + 576) + (1073741824:M)^2*((192:M) + 576) + (1073741824:M)^2*((2147483359:M) + 576))) + 7*((128:M)) + 5*(((1073741824:M)^1)*((2147483583:M)) + ((1073741824:M)^2)*((48:M) + 576) + ((1073741824:M)^2)*((2147483575:M))) := by
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
  rw [gatherGather251, gather251]
  rw [hwe 249 (by omega), hwe 251 (by omega), hwe 253 (by omega), hwo 248 (by omega), hwo 250 (by omega), hwo 251 (by omega), hwo 252 (by omega)]
  change -5*(w (2*251) - ((1073741824:M)*w (2*251) + (1073741824:M)^2*w (2*249) + (1073741824:M)^2*w (2*253))) + 7*w (2*251+1) + 5*(((1073741824:M)^1)*w (2*250+1) + ((1073741824:M)^2)*w (2*248+1) + ((1073741824:M)^2)*w (2*252+1)) = -5*(((2147483391:M) + 576) - ((1073741824:M)*((2147483391:M) + 576) + (1073741824:M)^2*((192:M) + 576) + (1073741824:M)^2*((2147483359:M) + 576))) + 7*((128:M)) + 5*(((1073741824:M)^1)*((2147483583:M)) + ((1073741824:M)^2)*((48:M) + 576) + ((1073741824:M)^2)*((2147483575:M)))
  rw [transport_leaf_0497, transport_leaf_0498, transport_leaf_0501, transport_leaf_0502, transport_leaf_0503, transport_leaf_0505, transport_leaf_0506]
#print axioms pw_0503

/-- finite source-only pointWeight expansion at 504; no field reduction --/
lemma pw_0504 : pw 504 = 7*((144:M) + 576) + 5*((2147483359:M) + 576) - 5*((2147483575:M)) := by
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
  rw [gather252]
  rw [hwe 252 (by omega), hwe 253 (by omega), hwo 252 (by omega)]
  change 7*w (2*252) + 5*(w (2*253)) - 5*w (2*252+1) = 7*((144:M) + 576) + 5*((2147483359:M) + 576) - 5*((2147483575:M))
  rw [transport_leaf_0504, transport_leaf_0505, transport_leaf_0506]
#print axioms pw_0504

/-- finite source-only pointWeight expansion at 505; no field reduction --/
lemma pw_0505 : pw 505 = -5*(((144:M) + 576) - ((1073741824:M)*((144:M) + 576) + (1073741824:M)*((2147483455:M) + 576))) + 7*((2147483575:M)) + 5*((144:M)) := by
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
  rw [gatherGather252, gather252]
  rw [hwe 252 (by omega), hwe 254 (by omega), hwo 252 (by omega), hwo 253 (by omega)]
  change -5*(w (2*252) - ((1073741824:M)*w (2*252) + (1073741824:M)*w (2*254))) + 7*w (2*252+1) + 5*(w (2*253+1)) = -5*(((144:M) + 576) - ((1073741824:M)*((144:M) + 576) + (1073741824:M)*((2147483455:M) + 576))) + 7*((2147483575:M)) + 5*((144:M))
  rw [transport_leaf_0504, transport_leaf_0505, transport_leaf_0507, transport_leaf_0508]
#print axioms pw_0505

/-- finite source-only pointWeight expansion at 507; no field reduction --/
lemma pw_0507 : pw 507 = -5*(((2147483359:M) + 576) - ((1073741824:M)*((2147483359:M) + 576) + (1073741824:M)*((384:M) + 576))) + 7*((144:M)) + 5*(((1073741824:M)^1)*((2147483575:M)) + ((1073741824:M)^1)*((96:M))) := by
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
  rw [gatherGather253, gather253]
  rw [hwe 253 (by omega), hwe 255 (by omega), hwo 252 (by omega), hwo 253 (by omega), hwo 254 (by omega)]
  change -5*(w (2*253) - ((1073741824:M)*w (2*253) + (1073741824:M)*w (2*255))) + 7*w (2*253+1) + 5*(((1073741824:M)^1)*w (2*252+1) + ((1073741824:M)^1)*w (2*254+1)) = -5*(((2147483359:M) + 576) - ((1073741824:M)*((2147483359:M) + 576) + (1073741824:M)*((384:M) + 576))) + 7*((144:M)) + 5*(((1073741824:M)^1)*((2147483575:M)) + ((1073741824:M)^1)*((96:M)))
  rw [transport_leaf_0505, transport_leaf_0506, transport_leaf_0507, transport_leaf_0509, transport_leaf_0510]
#print axioms pw_0507

/-- finite source-only pointWeight expansion at 508; no field reduction --/
lemma pw_0508 : pw 508 = 7*((2147483455:M) + 576) + 5*((384:M) + 576) - 5*((96:M)) := by
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
  rw [gather254]
  rw [hwe 254 (by omega), hwe 255 (by omega), hwo 254 (by omega)]
  change 7*w (2*254) + 5*(w (2*255)) - 5*w (2*254+1) = 7*((2147483455:M) + 576) + 5*((384:M) + 576) - 5*((96:M))
  rw [transport_leaf_0508, transport_leaf_0509, transport_leaf_0510]
#print axioms pw_0508

/-- finite source-only pointWeight expansion at 509; no field reduction --/
lemma pw_0509 : pw 509 = -5*(((2147483455:M) + 576) - ((1073741824:M)*((2147483455:M) + 576) + (1073741824:M)^2*((144:M) + 576) + (1073741824:M)^3*((2147483551:M) + 576) + (1073741824:M)^4*((48:M) + 576) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^6*((576 : M)) + (1073741824:M)^7*((576 : M)) + (1073741824:M)^8*((576:M)) + (1073741824:M)^8*((576 : M)))) + 7*((96:M)) + 5*((2147483455:M)) := by
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
  rw [gatherGather254, gather254]
  rw [hwe 0 (by omega), hwe 128 (by omega), hwe 192 (by omega), hwe 224 (by omega), hwe 240 (by omega), hwe 248 (by omega), hwe 252 (by omega), hwe 254 (by omega), hwe 256 (by omega), hwo 254 (by omega), hwo 255 (by omega)]
  change -5*(w (2*254) - ((1073741824:M)*w (2*254) + (1073741824:M)^2*w (2*252) + (1073741824:M)^3*w (2*248) + (1073741824:M)^4*w (2*240) + (1073741824:M)^5*w (2*224) + (1073741824:M)^6*w (2*192) + (1073741824:M)^7*w (2*128) + (1073741824:M)^8*w (2*0) + (1073741824:M)^8*w (2*256))) + 7*w (2*254+1) + 5*(w (2*255+1)) = -5*(((2147483455:M) + 576) - ((1073741824:M)*((2147483455:M) + 576) + (1073741824:M)^2*((144:M) + 576) + (1073741824:M)^3*((2147483551:M) + 576) + (1073741824:M)^4*((48:M) + 576) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^6*((576 : M)) + (1073741824:M)^7*((576 : M)) + (1073741824:M)^8*((576:M)) + (1073741824:M)^8*((576 : M)))) + 7*((96:M)) + 5*((2147483455:M))
  rw [w_0, w_guarded_leaf_0256, w_guarded_leaf_0384, w_guarded_leaf_0448, transport_leaf_0480, transport_leaf_0496, transport_leaf_0504, transport_leaf_0508, transport_leaf_0509, transport_leaf_0511, w_guarded_leaf_0512]
#print axioms pw_0509

/-- finite source-only pointWeight expansion at 624; no field reduction --/
lemma pw_0624 : pw 624 = 7*((144:M) + 576) + 5*((2147483359:M)) - 5*((2147483575:M) + 576) := by
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
  rw [gather312]
  rw [hwe 312 (by omega), hwe 313 (by omega), hwo 312 (by omega)]
  change 7*w (2*312) + 5*(w (2*313)) - 5*w (2*312+1) = 7*((144:M) + 576) + 5*((2147483359:M)) - 5*((2147483575:M) + 576)
  rw [transport_leaf_0624, transport_leaf_0625, transport_leaf_0626]
#print axioms pw_0624

/-- finite source-only pointWeight expansion at 626; no field reduction --/
lemma pw_0626 : pw 626 = 7*((2147483359:M)) + 5*(((1073741824:M)^1)*((144:M) + 576) + ((1073741824:M)^1)*((2147483455:M))) - 5*((144:M) + 576) := by
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
  rw [gather313]
  rw [hwe 312 (by omega), hwe 313 (by omega), hwe 314 (by omega), hwo 313 (by omega)]
  change 7*w (2*313) + 5*(((1073741824:M)^1)*w (2*312) + ((1073741824:M)^1)*w (2*314)) - 5*w (2*313+1) = 7*((2147483359:M)) + 5*(((1073741824:M)^1)*((144:M) + 576) + ((1073741824:M)^1)*((2147483455:M))) - 5*((144:M) + 576)
  rw [transport_leaf_0624, transport_leaf_0626, transport_leaf_0627, transport_leaf_0628]
#print axioms pw_0626

/-- finite source-only pointWeight expansion at 628; no field reduction --/
lemma pw_0628 : pw 628 = 7*((2147483455:M)) + 5*((384:M)) - 5*((96:M) + 576) := by
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
  rw [gather314]
  rw [hwe 314 (by omega), hwe 315 (by omega), hwo 314 (by omega)]
  change 7*w (2*314) + 5*(w (2*315)) - 5*w (2*314+1) = 7*((2147483455:M)) + 5*((384:M)) - 5*((96:M) + 576)
  rw [transport_leaf_0628, transport_leaf_0629, transport_leaf_0630]
#print axioms pw_0628

/-- finite source-only pointWeight expansion at 629; no field reduction --/
lemma pw_0629 : pw 629 = -5*(((2147483455:M)) - ((1073741824:M)*((2147483455:M)) + (1073741824:M)^2*((144:M) + 576) + (1073741824:M)^2*((2147483431:M)))) + 7*((96:M) + 576) + 5*((2147483455:M) + 576) := by
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
  rw [gatherGather314, gather314]
  rw [hwe 312 (by omega), hwe 314 (by omega), hwe 316 (by omega), hwo 314 (by omega), hwo 315 (by omega)]
  change -5*(w (2*314) - ((1073741824:M)*w (2*314) + (1073741824:M)^2*w (2*312) + (1073741824:M)^2*w (2*316))) + 7*w (2*314+1) + 5*(w (2*315+1)) = -5*(((2147483455:M)) - ((1073741824:M)*((2147483455:M)) + (1073741824:M)^2*((144:M) + 576) + (1073741824:M)^2*((2147483431:M)))) + 7*((96:M) + 576) + 5*((2147483455:M) + 576)
  rw [transport_leaf_0624, transport_leaf_0628, transport_leaf_0629, transport_leaf_0631, transport_leaf_0632]
#print axioms pw_0629

/-- finite source-only pointWeight expansion at 630; no field reduction --/
lemma pw_0630 : pw 630 = 7*((384:M)) + 5*(((1073741824:M)^1)*((2147483455:M)) + ((1073741824:M)^2)*((144:M) + 576) + ((1073741824:M)^2)*((2147483431:M))) - 5*((2147483455:M) + 576) := by
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
  rw [gather315]
  rw [hwe 312 (by omega), hwe 314 (by omega), hwe 315 (by omega), hwe 316 (by omega), hwo 315 (by omega)]
  change 7*w (2*315) + 5*(((1073741824:M)^1)*w (2*314) + ((1073741824:M)^2)*w (2*312) + ((1073741824:M)^2)*w (2*316)) - 5*w (2*315+1) = 7*((384:M)) + 5*(((1073741824:M)^1)*((2147483455:M)) + ((1073741824:M)^2)*((144:M) + 576) + ((1073741824:M)^2)*((2147483431:M))) - 5*((2147483455:M) + 576)
  rw [transport_leaf_0624, transport_leaf_0628, transport_leaf_0630, transport_leaf_0631, transport_leaf_0632]
#print axioms pw_0630

/-- finite source-only pointWeight expansion at 632; no field reduction --/
lemma pw_0632 : pw 632 = 7*((2147483431:M)) + 5*((432:M)) - 5*((108:M) + 576) := by
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
  rw [gather316]
  rw [hwe 316 (by omega), hwe 317 (by omega), hwo 316 (by omega)]
  change 7*w (2*316) + 5*(w (2*317)) - 5*w (2*316+1) = 7*((2147483431:M)) + 5*((432:M)) - 5*((108:M) + 576)
  rw [transport_leaf_0632, transport_leaf_0633, transport_leaf_0634]
#print axioms pw_0632

/-- finite source-only pointWeight expansion at 633; no field reduction --/
lemma pw_0633 : pw 633 = -5*(((2147483431:M)) - ((1073741824:M)*((2147483431:M)) + (1073741824:M)*((288:M)))) + 7*((108:M) + 576) + 5*((2147483431:M) + 576) := by
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
  rw [gatherGather316, gather316]
  rw [hwe 316 (by omega), hwe 318 (by omega), hwo 316 (by omega), hwo 317 (by omega)]
  change -5*(w (2*316) - ((1073741824:M)*w (2*316) + (1073741824:M)*w (2*318))) + 7*w (2*316+1) + 5*(w (2*317+1)) = -5*(((2147483431:M)) - ((1073741824:M)*((2147483431:M)) + (1073741824:M)*((288:M)))) + 7*((108:M) + 576) + 5*((2147483431:M) + 576)
  rw [transport_leaf_0632, transport_leaf_0633, transport_leaf_0635, transport_leaf_0636]
#print axioms pw_0633

/-- finite source-only pointWeight expansion at 634; no field reduction --/
lemma pw_0634 : pw 634 = 7*((432:M)) + 5*(((1073741824:M)^1)*((2147483431:M)) + ((1073741824:M)^1)*((288:M))) - 5*((2147483431:M) + 576) := by
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
  rw [gather317]
  rw [hwe 316 (by omega), hwe 317 (by omega), hwe 318 (by omega), hwo 317 (by omega)]
  change 7*w (2*317) + 5*(((1073741824:M)^1)*w (2*316) + ((1073741824:M)^1)*w (2*318)) - 5*w (2*317+1) = 7*((432:M)) + 5*(((1073741824:M)^1)*((2147483431:M)) + ((1073741824:M)^1)*((288:M))) - 5*((2147483431:M) + 576)
  rw [transport_leaf_0632, transport_leaf_0634, transport_leaf_0635, transport_leaf_0636]
#print axioms pw_0634

end
end AspisV8R19.R760PointWeightChunk06
