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

namespace AspisV8R19.R760PointWeightChunk00
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

/-- finite source-only pointWeight expansion at 1; no field reduction --/
lemma pw_0001 : pw 1 = -5*(((576:M)) - ((1073741824:M)*((576:M)) + (1073741824:M)*((576 : M)))) + 7*((576:M)) + 5*((576:M)) := by
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
  rw [gatherGather0, gather0]
  rw [hwe 0 (by omega), hwe 2 (by omega), hwo 0 (by omega), hwo 1 (by omega)]
  change -5*(w (2*0) - ((1073741824:M)*w (2*0) + (1073741824:M)*w (2*2))) + 7*w (2*0+1) + 5*(w (2*1+1)) = -5*(((576:M)) - ((1073741824:M)*((576:M)) + (1073741824:M)*((576 : M)))) + 7*((576:M)) + 5*((576:M))
  rw [w_0, w_1, w_3, w_guarded_leaf_0004]
#print axioms pw_0001

/-- finite source-only pointWeight expansion at 2; no field reduction --/
lemma pw_0002 : pw 2 = 7*((576:M)) + 5*(((1073741824:M)^1)*((576:M)) + ((1073741824:M)^1)*((576 : M))) - 5*((576:M)) := by
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
  rw [gather1]
  rw [hwe 0 (by omega), hwe 1 (by omega), hwe 2 (by omega), hwo 1 (by omega)]
  change 7*w (2*1) + 5*(((1073741824:M)^1)*w (2*0) + ((1073741824:M)^1)*w (2*2)) - 5*w (2*1+1) = 7*((576:M)) + 5*(((1073741824:M)^1)*((576:M)) + ((1073741824:M)^1)*((576 : M))) - 5*((576:M))
  rw [w_0, w_2, w_3, w_guarded_leaf_0004]
#print axioms pw_0002

/-- finite source-only pointWeight expansion at 92; no field reduction --/
lemma pw_0092 : pw 92 = 7*((576 : M)) + 5*((576 : M)) - 5*((576 : M)) := by
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
  rw [gather46]
  rw [hwe 46 (by omega), hwe 47 (by omega), hwo 46 (by omega)]
  change 7*w (2*46) + 5*(w (2*47)) - 5*w (2*46+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0092, w_guarded_leaf_0093, w_guarded_leaf_0094]
#print axioms pw_0092

/-- finite source-only pointWeight expansion at 93; no field reduction --/
lemma pw_0093 : pw 93 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^4*((144:M) + 576))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather46, gather46]
  rw [hwe 32 (by omega), hwe 40 (by omega), hwe 44 (by omega), hwe 46 (by omega), hwe 48 (by omega), hwo 46 (by omega), hwo 47 (by omega)]
  change -5*(w (2*46) - ((1073741824:M)*w (2*46) + (1073741824:M)^2*w (2*44) + (1073741824:M)^3*w (2*40) + (1073741824:M)^4*w (2*32) + (1073741824:M)^4*w (2*48))) + 7*w (2*46+1) + 5*(w (2*47+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^4*((144:M) + 576))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0064, w_guarded_leaf_0080, w_guarded_leaf_0088, w_guarded_leaf_0092, w_guarded_leaf_0093, w_guarded_leaf_0095, transport_leaf_0096]
#print axioms pw_0093

/-- finite source-only pointWeight expansion at 94; no field reduction --/
lemma pw_0094 : pw 94 = 7*((576 : M)) + 5*(((1073741824:M)^1)*((576 : M)) + ((1073741824:M)^2)*((576 : M)) + ((1073741824:M)^3)*((576 : M)) + ((1073741824:M)^4)*((576 : M)) + ((1073741824:M)^4)*((144:M) + 576)) - 5*((576 : M)) := by
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
  rw [gather47]
  rw [hwe 32 (by omega), hwe 40 (by omega), hwe 44 (by omega), hwe 46 (by omega), hwe 47 (by omega), hwe 48 (by omega), hwo 47 (by omega)]
  change 7*w (2*47) + 5*(((1073741824:M)^1)*w (2*46) + ((1073741824:M)^2)*w (2*44) + ((1073741824:M)^3)*w (2*40) + ((1073741824:M)^4)*w (2*32) + ((1073741824:M)^4)*w (2*48)) - 5*w (2*47+1) = 7*((576 : M)) + 5*(((1073741824:M)^1)*((576 : M)) + ((1073741824:M)^2)*((576 : M)) + ((1073741824:M)^3)*((576 : M)) + ((1073741824:M)^4)*((576 : M)) + ((1073741824:M)^4)*((144:M) + 576)) - 5*((576 : M))
  rw [w_guarded_leaf_0064, w_guarded_leaf_0080, w_guarded_leaf_0088, w_guarded_leaf_0092, w_guarded_leaf_0094, w_guarded_leaf_0095, transport_leaf_0096]
#print axioms pw_0094

/-- finite source-only pointWeight expansion at 95; no field reduction --/
lemma pw_0095 : pw 95 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^4*((2147483359:M) + 576))) + 7*((576 : M)) + 5*(((1073741824:M)^1)*((576 : M)) + ((1073741824:M)^2)*((576 : M)) + ((1073741824:M)^3)*((576 : M)) + ((1073741824:M)^4)*((576 : M)) + ((1073741824:M)^4)*((2147483575:M) + 576)) := by
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
  rw [gatherGather47, gather47]
  rw [hwe 33 (by omega), hwe 41 (by omega), hwe 45 (by omega), hwe 47 (by omega), hwe 49 (by omega), hwo 32 (by omega), hwo 40 (by omega), hwo 44 (by omega), hwo 46 (by omega), hwo 47 (by omega), hwo 48 (by omega)]
  change -5*(w (2*47) - ((1073741824:M)*w (2*47) + (1073741824:M)^2*w (2*45) + (1073741824:M)^3*w (2*41) + (1073741824:M)^4*w (2*33) + (1073741824:M)^4*w (2*49))) + 7*w (2*47+1) + 5*(((1073741824:M)^1)*w (2*46+1) + ((1073741824:M)^2)*w (2*44+1) + ((1073741824:M)^3)*w (2*40+1) + ((1073741824:M)^4)*w (2*32+1) + ((1073741824:M)^4)*w (2*48+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^4*((2147483359:M) + 576))) + 7*((576 : M)) + 5*(((1073741824:M)^1)*((576 : M)) + ((1073741824:M)^2)*((576 : M)) + ((1073741824:M)^3)*((576 : M)) + ((1073741824:M)^4)*((576 : M)) + ((1073741824:M)^4)*((2147483575:M) + 576))
  rw [w_guarded_leaf_0065, w_guarded_leaf_0066, w_guarded_leaf_0081, w_guarded_leaf_0082, w_guarded_leaf_0089, w_guarded_leaf_0090, w_guarded_leaf_0093, w_guarded_leaf_0094, w_guarded_leaf_0095, transport_leaf_0097, transport_leaf_0098]
#print axioms pw_0095

/-- finite source-only pointWeight expansion at 96; no field reduction --/
lemma pw_0096 : pw 96 = 7*((144:M) + 576) + 5*((2147483359:M) + 576) - 5*((2147483575:M) + 576) := by
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
  rw [gather48]
  rw [hwe 48 (by omega), hwe 49 (by omega), hwo 48 (by omega)]
  change 7*w (2*48) + 5*(w (2*49)) - 5*w (2*48+1) = 7*((144:M) + 576) + 5*((2147483359:M) + 576) - 5*((2147483575:M) + 576)
  rw [transport_leaf_0096, transport_leaf_0097, transport_leaf_0098]
#print axioms pw_0096

/-- finite source-only pointWeight expansion at 97; no field reduction --/
lemma pw_0097 : pw 97 = -5*(((144:M) + 576) - ((1073741824:M)*((144:M) + 576) + (1073741824:M)*((2147483455:M) + 576))) + 7*((2147483575:M) + 576) + 5*((144:M) + 576) := by
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
  rw [gatherGather48, gather48]
  rw [hwe 48 (by omega), hwe 50 (by omega), hwo 48 (by omega), hwo 49 (by omega)]
  change -5*(w (2*48) - ((1073741824:M)*w (2*48) + (1073741824:M)*w (2*50))) + 7*w (2*48+1) + 5*(w (2*49+1)) = -5*(((144:M) + 576) - ((1073741824:M)*((144:M) + 576) + (1073741824:M)*((2147483455:M) + 576))) + 7*((2147483575:M) + 576) + 5*((144:M) + 576)
  rw [transport_leaf_0096, transport_leaf_0097, transport_leaf_0099, transport_leaf_0100]
#print axioms pw_0097

/-- finite source-only pointWeight expansion at 98; no field reduction --/
lemma pw_0098 : pw 98 = 7*((2147483359:M) + 576) + 5*(((1073741824:M)^1)*((144:M) + 576) + ((1073741824:M)^1)*((2147483455:M) + 576)) - 5*((144:M) + 576) := by
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
  rw [gather49]
  rw [hwe 48 (by omega), hwe 49 (by omega), hwe 50 (by omega), hwo 49 (by omega)]
  change 7*w (2*49) + 5*(((1073741824:M)^1)*w (2*48) + ((1073741824:M)^1)*w (2*50)) - 5*w (2*49+1) = 7*((2147483359:M) + 576) + 5*(((1073741824:M)^1)*((144:M) + 576) + ((1073741824:M)^1)*((2147483455:M) + 576)) - 5*((144:M) + 576)
  rw [transport_leaf_0096, transport_leaf_0098, transport_leaf_0099, transport_leaf_0100]
#print axioms pw_0098

/-- finite source-only pointWeight expansion at 99; no field reduction --/
lemma pw_0099 : pw 99 = -5*(((2147483359:M) + 576) - ((1073741824:M)*((2147483359:M) + 576) + (1073741824:M)*((384:M) + 576))) + 7*((144:M) + 576) + 5*(((1073741824:M)^1)*((2147483575:M) + 576) + ((1073741824:M)^1)*((96:M) + 576)) := by
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
  rw [gatherGather49, gather49]
  rw [hwe 49 (by omega), hwe 51 (by omega), hwo 48 (by omega), hwo 49 (by omega), hwo 50 (by omega)]
  change -5*(w (2*49) - ((1073741824:M)*w (2*49) + (1073741824:M)*w (2*51))) + 7*w (2*49+1) + 5*(((1073741824:M)^1)*w (2*48+1) + ((1073741824:M)^1)*w (2*50+1)) = -5*(((2147483359:M) + 576) - ((1073741824:M)*((2147483359:M) + 576) + (1073741824:M)*((384:M) + 576))) + 7*((144:M) + 576) + 5*(((1073741824:M)^1)*((2147483575:M) + 576) + ((1073741824:M)^1)*((96:M) + 576))
  rw [transport_leaf_0097, transport_leaf_0098, transport_leaf_0099, transport_leaf_0101, transport_leaf_0102]
#print axioms pw_0099

/-- finite source-only pointWeight expansion at 108; no field reduction --/
lemma pw_0108 : pw 108 = 7*((288:M) + 576) + 5*((2147483071:M) + 576) - 5*((2147483503:M) + 576) := by
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
  rw [gather54]
  rw [hwe 54 (by omega), hwe 55 (by omega), hwo 54 (by omega)]
  change 7*w (2*54) + 5*(w (2*55)) - 5*w (2*54+1) = 7*((288:M) + 576) + 5*((2147483071:M) + 576) - 5*((2147483503:M) + 576)
  rw [transport_leaf_0108, transport_leaf_0109, transport_leaf_0110]
#print axioms pw_0108

/-- finite source-only pointWeight expansion at 111; no field reduction --/
lemma pw_0111 : pw 111 = -5*(((2147483071:M) + 576) - ((1073741824:M)*((2147483071:M) + 576) + (1073741824:M)^2*((432:M) + 576) + (1073741824:M)^3*((2147483359:M) + 576) + (1073741824:M)^3*((576:M)))) + 7*((288:M) + 576) + 5*(((1073741824:M)^1)*((2147483503:M) + 576) + ((1073741824:M)^2)*((108:M) + 576) + ((1073741824:M)^3)*((2147483575:M) + 576) + ((1073741824:M)^3)*((144:M) + 576)) := by
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
  rw [gatherGather55, gather55]
  rw [hwe 49 (by omega), hwe 53 (by omega), hwe 55 (by omega), hwe 57 (by omega), hwo 48 (by omega), hwo 52 (by omega), hwo 54 (by omega), hwo 55 (by omega), hwo 56 (by omega)]
  change -5*(w (2*55) - ((1073741824:M)*w (2*55) + (1073741824:M)^2*w (2*53) + (1073741824:M)^3*w (2*49) + (1073741824:M)^3*w (2*57))) + 7*w (2*55+1) + 5*(((1073741824:M)^1)*w (2*54+1) + ((1073741824:M)^2)*w (2*52+1) + ((1073741824:M)^3)*w (2*48+1) + ((1073741824:M)^3)*w (2*56+1)) = -5*(((2147483071:M) + 576) - ((1073741824:M)*((2147483071:M) + 576) + (1073741824:M)^2*((432:M) + 576) + (1073741824:M)^3*((2147483359:M) + 576) + (1073741824:M)^3*((576:M)))) + 7*((288:M) + 576) + 5*(((1073741824:M)^1)*((2147483503:M) + 576) + ((1073741824:M)^2)*((108:M) + 576) + ((1073741824:M)^3)*((2147483575:M) + 576) + ((1073741824:M)^3)*((144:M) + 576))
  rw [transport_leaf_0097, transport_leaf_0098, transport_leaf_0105, transport_leaf_0106, transport_leaf_0109, transport_leaf_0110, transport_leaf_0111, transport_leaf_0113, transport_leaf_0114]
#print axioms pw_0111

/-- finite source-only pointWeight expansion at 112; no field reduction --/
lemma pw_0112 : pw 112 = 7*((2147483359:M) + 576) + 5*((576:M)) - 5*((144:M) + 576) := by
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
  rw [gather56]
  rw [hwe 56 (by omega), hwe 57 (by omega), hwo 56 (by omega)]
  change 7*w (2*56) + 5*(w (2*57)) - 5*w (2*56+1) = 7*((2147483359:M) + 576) + 5*((576:M)) - 5*((144:M) + 576)
  rw [transport_leaf_0112, transport_leaf_0113, transport_leaf_0114]
#print axioms pw_0112

/-- finite source-only pointWeight expansion at 114; no field reduction --/
lemma pw_0114 : pw 114 = 7*((576:M)) + 5*(((1073741824:M)^1)*((2147483359:M) + 576) + ((1073741824:M)^1)*((384:M))) - 5*((2147483359:M) + 576) := by
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
  rw [gather57]
  rw [hwe 56 (by omega), hwe 57 (by omega), hwe 58 (by omega), hwo 57 (by omega)]
  change 7*w (2*57) + 5*(((1073741824:M)^1)*w (2*56) + ((1073741824:M)^1)*w (2*58)) - 5*w (2*57+1) = 7*((576:M)) + 5*(((1073741824:M)^1)*((2147483359:M) + 576) + ((1073741824:M)^1)*((384:M))) - 5*((2147483359:M) + 576)
  rw [transport_leaf_0112, transport_leaf_0114, transport_leaf_0115, transport_leaf_0116]
#print axioms pw_0114

/-- finite source-only pointWeight expansion at 116; no field reduction --/
lemma pw_0116 : pw 116 = 7*((384:M)) + 5*((2147482879:M)) - 5*((2147483455:M) + 576) := by
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
  rw [gather58]
  rw [hwe 58 (by omega), hwe 59 (by omega), hwo 58 (by omega)]
  change 7*w (2*58) + 5*(w (2*59)) - 5*w (2*58+1) = 7*((384:M)) + 5*((2147482879:M)) - 5*((2147483455:M) + 576)
  rw [transport_leaf_0116, transport_leaf_0117, transport_leaf_0118]
#print axioms pw_0116

/-- finite source-only pointWeight expansion at 117; no field reduction --/
lemma pw_0117 : pw 117 = -5*(((384:M)) - ((1073741824:M)*((384:M)) + (1073741824:M)^2*((2147483359:M) + 576) + (1073741824:M)^2*((432:M)))) + 7*((2147483455:M) + 576) + 5*((384:M) + 576) := by
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
  rw [gatherGather58, gather58]
  rw [hwe 56 (by omega), hwe 58 (by omega), hwe 60 (by omega), hwo 58 (by omega), hwo 59 (by omega)]
  change -5*(w (2*58) - ((1073741824:M)*w (2*58) + (1073741824:M)^2*w (2*56) + (1073741824:M)^2*w (2*60))) + 7*w (2*58+1) + 5*(w (2*59+1)) = -5*(((384:M)) - ((1073741824:M)*((384:M)) + (1073741824:M)^2*((2147483359:M) + 576) + (1073741824:M)^2*((432:M)))) + 7*((2147483455:M) + 576) + 5*((384:M) + 576)
  rw [transport_leaf_0112, transport_leaf_0116, transport_leaf_0117, transport_leaf_0119, transport_leaf_0120]
#print axioms pw_0117

/-- finite source-only pointWeight expansion at 118; no field reduction --/
lemma pw_0118 : pw 118 = 7*((2147482879:M)) + 5*(((1073741824:M)^1)*((384:M)) + ((1073741824:M)^2)*((2147483359:M) + 576) + ((1073741824:M)^2)*((432:M))) - 5*((384:M) + 576) := by
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
  rw [gather59]
  rw [hwe 56 (by omega), hwe 58 (by omega), hwe 59 (by omega), hwe 60 (by omega), hwo 59 (by omega)]
  change 7*w (2*59) + 5*(((1073741824:M)^1)*w (2*58) + ((1073741824:M)^2)*w (2*56) + ((1073741824:M)^2)*w (2*60)) - 5*w (2*59+1) = 7*((2147482879:M)) + 5*(((1073741824:M)^1)*((384:M)) + ((1073741824:M)^2)*((2147483359:M) + 576) + ((1073741824:M)^2)*((432:M))) - 5*((384:M) + 576)
  rw [transport_leaf_0112, transport_leaf_0116, transport_leaf_0118, transport_leaf_0119, transport_leaf_0120]
#print axioms pw_0118

/-- finite source-only pointWeight expansion at 120; no field reduction --/
lemma pw_0120 : pw 120 = 7*((432:M)) + 5*((2147482783:M)) - 5*((2147483431:M) + 576) := by
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
  rw [gather60]
  rw [hwe 60 (by omega), hwe 61 (by omega), hwo 60 (by omega)]
  change 7*w (2*60) + 5*(w (2*61)) - 5*w (2*60+1) = 7*((432:M)) + 5*((2147482783:M)) - 5*((2147483431:M) + 576)
  rw [transport_leaf_0120, transport_leaf_0121, transport_leaf_0122]
#print axioms pw_0120

/-- finite source-only pointWeight expansion at 121; no field reduction --/
lemma pw_0121 : pw 121 = -5*(((432:M)) - ((1073741824:M)*((432:M)) + (1073741824:M)*((2147483071:M)))) + 7*((2147483431:M) + 576) + 5*((432:M) + 576) := by
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
  rw [gatherGather60, gather60]
  rw [hwe 60 (by omega), hwe 62 (by omega), hwo 60 (by omega), hwo 61 (by omega)]
  change -5*(w (2*60) - ((1073741824:M)*w (2*60) + (1073741824:M)*w (2*62))) + 7*w (2*60+1) + 5*(w (2*61+1)) = -5*(((432:M)) - ((1073741824:M)*((432:M)) + (1073741824:M)*((2147483071:M)))) + 7*((2147483431:M) + 576) + 5*((432:M) + 576)
  rw [transport_leaf_0120, transport_leaf_0121, transport_leaf_0123, transport_leaf_0124]
#print axioms pw_0121

/-- finite source-only pointWeight expansion at 122; no field reduction --/
lemma pw_0122 : pw 122 = 7*((2147482783:M)) + 5*(((1073741824:M)^1)*((432:M)) + ((1073741824:M)^1)*((2147483071:M))) - 5*((432:M) + 576) := by
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
  rw [gather61]
  rw [hwe 60 (by omega), hwe 61 (by omega), hwe 62 (by omega), hwo 61 (by omega)]
  change 7*w (2*61) + 5*(((1073741824:M)^1)*w (2*60) + ((1073741824:M)^1)*w (2*62)) - 5*w (2*61+1) = 7*((2147482783:M)) + 5*(((1073741824:M)^1)*((432:M)) + ((1073741824:M)^1)*((2147483071:M))) - 5*((432:M) + 576)
  rw [transport_leaf_0120, transport_leaf_0122, transport_leaf_0123, transport_leaf_0124]
#print axioms pw_0122

/-- finite source-only pointWeight expansion at 124; no field reduction --/
lemma pw_0124 : pw 124 = 7*((2147483071:M)) + 5*((2147483599:M)) - 5*((288:M) + 576) := by
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
  rw [gather62]
  rw [hwe 62 (by omega), hwe 63 (by omega), hwo 62 (by omega)]
  change 7*w (2*62) + 5*(w (2*63)) - 5*w (2*62+1) = 7*((2147483071:M)) + 5*((2147483599:M)) - 5*((288:M) + 576)
  rw [transport_leaf_0124, transport_leaf_0125, transport_leaf_0126]
#print axioms pw_0124

/-- finite source-only pointWeight expansion at 125; no field reduction --/
lemma pw_0125 : pw 125 = -5*(((2147483071:M)) - ((1073741824:M)*((2147483071:M)) + (1073741824:M)^2*((432:M)) + (1073741824:M)^3*((2147483359:M) + 576) + (1073741824:M)^4*((144:M) + 576) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^6*((576:M)) + (1073741824:M)^6*((0 : M)))) + 7*((288:M) + 576) + 5*((96:M) + 576) := by
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
  rw [gatherGather62, gather62]
  rw [hwe 0 (by omega), hwe 32 (by omega), hwe 48 (by omega), hwe 56 (by omega), hwe 60 (by omega), hwe 62 (by omega), hwe 64 (by omega), hwo 62 (by omega), hwo 63 (by omega)]
  change -5*(w (2*62) - ((1073741824:M)*w (2*62) + (1073741824:M)^2*w (2*60) + (1073741824:M)^3*w (2*56) + (1073741824:M)^4*w (2*48) + (1073741824:M)^5*w (2*32) + (1073741824:M)^6*w (2*0) + (1073741824:M)^6*w (2*64))) + 7*w (2*62+1) + 5*(w (2*63+1)) = -5*(((2147483071:M)) - ((1073741824:M)*((2147483071:M)) + (1073741824:M)^2*((432:M)) + (1073741824:M)^3*((2147483359:M) + 576) + (1073741824:M)^4*((144:M) + 576) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^6*((576:M)) + (1073741824:M)^6*((0 : M)))) + 7*((288:M) + 576) + 5*((96:M) + 576)
  rw [w_0, w_guarded_leaf_0064, transport_leaf_0096, transport_leaf_0112, transport_leaf_0120, transport_leaf_0124, transport_leaf_0125, transport_leaf_0127, w_guarded_leaf_0128]
#print axioms pw_0125

/-- finite source-only pointWeight expansion at 126; no field reduction --/
lemma pw_0126 : pw 126 = 7*((2147483599:M)) + 5*(((1073741824:M)^1)*((2147483071:M)) + ((1073741824:M)^2)*((432:M)) + ((1073741824:M)^3)*((2147483359:M) + 576) + ((1073741824:M)^4)*((144:M) + 576) + ((1073741824:M)^5)*((576 : M)) + ((1073741824:M)^6)*((576:M)) + ((1073741824:M)^6)*((0 : M))) - 5*((96:M) + 576) := by
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
  rw [gather63]
  rw [hwe 0 (by omega), hwe 32 (by omega), hwe 48 (by omega), hwe 56 (by omega), hwe 60 (by omega), hwe 62 (by omega), hwe 63 (by omega), hwe 64 (by omega), hwo 63 (by omega)]
  change 7*w (2*63) + 5*(((1073741824:M)^1)*w (2*62) + ((1073741824:M)^2)*w (2*60) + ((1073741824:M)^3)*w (2*56) + ((1073741824:M)^4)*w (2*48) + ((1073741824:M)^5)*w (2*32) + ((1073741824:M)^6)*w (2*0) + ((1073741824:M)^6)*w (2*64)) - 5*w (2*63+1) = 7*((2147483599:M)) + 5*(((1073741824:M)^1)*((2147483071:M)) + ((1073741824:M)^2)*((432:M)) + ((1073741824:M)^3)*((2147483359:M) + 576) + ((1073741824:M)^4)*((144:M) + 576) + ((1073741824:M)^5)*((576 : M)) + ((1073741824:M)^6)*((576:M)) + ((1073741824:M)^6)*((0 : M))) - 5*((96:M) + 576)
  rw [w_0, w_guarded_leaf_0064, transport_leaf_0096, transport_leaf_0112, transport_leaf_0120, transport_leaf_0124, transport_leaf_0126, transport_leaf_0127, w_guarded_leaf_0128]
#print axioms pw_0126

/-- finite source-only pointWeight expansion at 128; no field reduction --/
lemma pw_0128 : pw 128 = 7*((0 : M)) + 5*((0:M)) - 5*((576:M)) := by
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
  rw [gather64]
  rw [hwe 64 (by omega), hwe 65 (by omega), hwo 64 (by omega)]
  change 7*w (2*64) + 5*(w (2*65)) - 5*w (2*64+1) = 7*((0 : M)) + 5*((0:M)) - 5*((576:M))
  rw [w_guarded_leaf_0128, w_129, w_130]
#print axioms pw_0128

/-- finite source-only pointWeight expansion at 129; no field reduction --/
lemma pw_0129 : pw 129 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576:M)) + 5*((576 : M)) := by
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
  rw [gatherGather64, gather64]
  rw [hwe 64 (by omega), hwe 66 (by omega), hwo 64 (by omega), hwo 65 (by omega)]
  change -5*(w (2*64) - ((1073741824:M)*w (2*64) + (1073741824:M)*w (2*66))) + 7*w (2*64+1) + 5*(w (2*65+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576:M)) + 5*((576 : M))
  rw [w_guarded_leaf_0128, w_129, w_guarded_leaf_0131, w_guarded_leaf_0132]
#print axioms pw_0129

/-- finite source-only pointWeight expansion at 130; no field reduction --/
lemma pw_0130 : pw 130 = 7*((0:M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather65]
  rw [hwe 64 (by omega), hwe 65 (by omega), hwe 66 (by omega), hwo 65 (by omega)]
  change 7*w (2*65) + 5*(((1073741824:M)^1)*w (2*64) + ((1073741824:M)^1)*w (2*66)) - 5*w (2*65+1) = 7*((0:M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0128, w_130, w_guarded_leaf_0131, w_guarded_leaf_0132]
#print axioms pw_0130

/-- finite source-only pointWeight expansion at 132; no field reduction --/
lemma pw_0132 : pw 132 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather66]
  rw [hwe 66 (by omega), hwe 67 (by omega), hwo 66 (by omega)]
  change 7*w (2*66) + 5*(w (2*67)) - 5*w (2*66+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0132, w_guarded_leaf_0133, w_guarded_leaf_0134]
#print axioms pw_0132

/-- finite source-only pointWeight expansion at 133; no field reduction --/
lemma pw_0133 : pw 133 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather66, gather66]
  rw [hwe 64 (by omega), hwe 66 (by omega), hwe 68 (by omega), hwo 66 (by omega), hwo 67 (by omega)]
  change -5*(w (2*66) - ((1073741824:M)*w (2*66) + (1073741824:M)^2*w (2*64) + (1073741824:M)^2*w (2*68))) + 7*w (2*66+1) + 5*(w (2*67+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0128, w_guarded_leaf_0132, w_guarded_leaf_0133, w_guarded_leaf_0135, w_guarded_leaf_0136]
#print axioms pw_0133

/-- finite source-only pointWeight expansion at 134; no field reduction --/
lemma pw_0134 : pw 134 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather67]
  rw [hwe 64 (by omega), hwe 66 (by omega), hwe 67 (by omega), hwe 68 (by omega), hwo 67 (by omega)]
  change 7*w (2*67) + 5*(((1073741824:M)^1)*w (2*66) + ((1073741824:M)^2)*w (2*64) + ((1073741824:M)^2)*w (2*68)) - 5*w (2*67+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0128, w_guarded_leaf_0132, w_guarded_leaf_0134, w_guarded_leaf_0135, w_guarded_leaf_0136]
#print axioms pw_0134

/-- finite source-only pointWeight expansion at 136; no field reduction --/
lemma pw_0136 : pw 136 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather68]
  rw [hwe 68 (by omega), hwe 69 (by omega), hwo 68 (by omega)]
  change 7*w (2*68) + 5*(w (2*69)) - 5*w (2*68+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0136, w_guarded_leaf_0137, w_guarded_leaf_0138]
#print axioms pw_0136

/-- finite source-only pointWeight expansion at 137; no field reduction --/
lemma pw_0137 : pw 137 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather68, gather68]
  rw [hwe 68 (by omega), hwe 70 (by omega), hwo 68 (by omega), hwo 69 (by omega)]
  change -5*(w (2*68) - ((1073741824:M)*w (2*68) + (1073741824:M)*w (2*70))) + 7*w (2*68+1) + 5*(w (2*69+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0136, w_guarded_leaf_0137, w_guarded_leaf_0139, w_guarded_leaf_0140]
#print axioms pw_0137

/-- finite source-only pointWeight expansion at 138; no field reduction --/
lemma pw_0138 : pw 138 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather69]
  rw [hwe 68 (by omega), hwe 69 (by omega), hwe 70 (by omega), hwo 69 (by omega)]
  change 7*w (2*69) + 5*(((1073741824:M)^1)*w (2*68) + ((1073741824:M)^1)*w (2*70)) - 5*w (2*69+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0136, w_guarded_leaf_0138, w_guarded_leaf_0139, w_guarded_leaf_0140]
#print axioms pw_0138

end
end AspisV8R19.R760PointWeightChunk00
