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

namespace AspisV8R19.R760PointWeightChunk10
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

/-- finite source-only pointWeight expansion at 997; no field reduction --/
lemma pw_0997 : pw 997 = -5*(((32:M)) - ((1073741824:M)*((32:M)) + (1073741824:M)^2*((2147483623:M)) + (1073741824:M)^2*((36:M)))) + 7*((2147483631:M) + 576) + 5*((32:M) + 576) := by
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
  rw [gatherGather498, gather498]
  rw [hwe 496 (by omega), hwe 498 (by omega), hwe 500 (by omega), hwo 498 (by omega), hwo 499 (by omega)]
  change -5*(w (2*498) - ((1073741824:M)*w (2*498) + (1073741824:M)^2*w (2*496) + (1073741824:M)^2*w (2*500))) + 7*w (2*498+1) + 5*(w (2*499+1)) = -5*(((32:M)) - ((1073741824:M)*((32:M)) + (1073741824:M)^2*((2147483623:M)) + (1073741824:M)^2*((36:M)))) + 7*((2147483631:M) + 576) + 5*((32:M) + 576)
  rw [transport_leaf_0992, transport_leaf_0996, transport_leaf_0997, transport_leaf_0999, transport_leaf_1000]
#print axioms pw_0997

/-- finite source-only pointWeight expansion at 998; no field reduction --/
lemma pw_0998 : pw 998 = 7*((2147483583:M)) + 5*(((1073741824:M)^1)*((32:M)) + ((1073741824:M)^2)*((2147483623:M)) + ((1073741824:M)^2)*((36:M))) - 5*((32:M) + 576) := by
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
  rw [gather499]
  rw [hwe 496 (by omega), hwe 498 (by omega), hwe 499 (by omega), hwe 500 (by omega), hwo 499 (by omega)]
  change 7*w (2*499) + 5*(((1073741824:M)^1)*w (2*498) + ((1073741824:M)^2)*w (2*496) + ((1073741824:M)^2)*w (2*500)) - 5*w (2*499+1) = 7*((2147483583:M)) + 5*(((1073741824:M)^1)*((32:M)) + ((1073741824:M)^2)*((2147483623:M)) + ((1073741824:M)^2)*((36:M))) - 5*((32:M) + 576)
  rw [transport_leaf_0992, transport_leaf_0996, transport_leaf_0998, transport_leaf_0999, transport_leaf_1000]
#print axioms pw_0998

/-- finite source-only pointWeight expansion at 1000; no field reduction --/
lemma pw_1000 : pw 1000 = 7*((36:M)) + 5*((2147483575:M)) - 5*((2147483629:M) + 576) := by
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
  rw [gather500]
  rw [hwe 500 (by omega), hwe 501 (by omega), hwo 500 (by omega)]
  change 7*w (2*500) + 5*(w (2*501)) - 5*w (2*500+1) = 7*((36:M)) + 5*((2147483575:M)) - 5*((2147483629:M) + 576)
  rw [transport_leaf_1000, transport_leaf_1001, transport_leaf_1002]
#print axioms pw_1000

/-- finite source-only pointWeight expansion at 1001; no field reduction --/
lemma pw_1001 : pw 1001 = -5*(((36:M)) - ((1073741824:M)*((36:M)) + (1073741824:M)*((2147483599:M)))) + 7*((2147483629:M) + 576) + 5*((36:M) + 576) := by
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
  rw [gatherGather500, gather500]
  rw [hwe 500 (by omega), hwe 502 (by omega), hwo 500 (by omega), hwo 501 (by omega)]
  change -5*(w (2*500) - ((1073741824:M)*w (2*500) + (1073741824:M)*w (2*502))) + 7*w (2*500+1) + 5*(w (2*501+1)) = -5*(((36:M)) - ((1073741824:M)*((36:M)) + (1073741824:M)*((2147483599:M)))) + 7*((2147483629:M) + 576) + 5*((36:M) + 576)
  rw [transport_leaf_1000, transport_leaf_1001, transport_leaf_1003, transport_leaf_1004]
#print axioms pw_1001

/-- finite source-only pointWeight expansion at 1002; no field reduction --/
lemma pw_1002 : pw 1002 = 7*((2147483575:M)) + 5*(((1073741824:M)^1)*((36:M)) + ((1073741824:M)^1)*((2147483599:M))) - 5*((36:M) + 576) := by
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
  rw [gather501]
  rw [hwe 500 (by omega), hwe 501 (by omega), hwe 502 (by omega), hwo 501 (by omega)]
  change 7*w (2*501) + 5*(((1073741824:M)^1)*w (2*500) + ((1073741824:M)^1)*w (2*502)) - 5*w (2*501+1) = 7*((2147483575:M)) + 5*(((1073741824:M)^1)*((36:M)) + ((1073741824:M)^1)*((2147483599:M))) - 5*((36:M) + 576)
  rw [transport_leaf_1000, transport_leaf_1002, transport_leaf_1003, transport_leaf_1004]
#print axioms pw_1002

/-- finite source-only pointWeight expansion at 1004; no field reduction --/
lemma pw_1004 : pw 1004 = 7*((2147483599:M)) + 5*((96:M)) - 5*((24:M) + 576) := by
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
  rw [gather502]
  rw [hwe 502 (by omega), hwe 503 (by omega), hwo 502 (by omega)]
  change 7*w (2*502) + 5*(w (2*503)) - 5*w (2*502+1) = 7*((2147483599:M)) + 5*((96:M)) - 5*((24:M) + 576)
  rw [transport_leaf_1004, transport_leaf_1005, transport_leaf_1006]
#print axioms pw_1004

/-- finite source-only pointWeight expansion at 1005; no field reduction --/
lemma pw_1005 : pw 1005 = -5*(((2147483599:M)) - ((1073741824:M)*((2147483599:M)) + (1073741824:M)^2*((36:M)) + (1073741824:M)^3*((2147483623:M)) + (1073741824:M)^3*((48:M)))) + 7*((24:M) + 576) + 5*((2147483599:M) + 576) := by
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
  rw [gatherGather502, gather502]
  rw [hwe 496 (by omega), hwe 500 (by omega), hwe 502 (by omega), hwe 504 (by omega), hwo 502 (by omega), hwo 503 (by omega)]
  change -5*(w (2*502) - ((1073741824:M)*w (2*502) + (1073741824:M)^2*w (2*500) + (1073741824:M)^3*w (2*496) + (1073741824:M)^3*w (2*504))) + 7*w (2*502+1) + 5*(w (2*503+1)) = -5*(((2147483599:M)) - ((1073741824:M)*((2147483599:M)) + (1073741824:M)^2*((36:M)) + (1073741824:M)^3*((2147483623:M)) + (1073741824:M)^3*((48:M)))) + 7*((24:M) + 576) + 5*((2147483599:M) + 576)
  rw [transport_leaf_0992, transport_leaf_1000, transport_leaf_1004, transport_leaf_1005, transport_leaf_1007, transport_leaf_1008]
#print axioms pw_1005

/-- finite source-only pointWeight expansion at 1006; no field reduction --/
lemma pw_1006 : pw 1006 = 7*((96:M)) + 5*(((1073741824:M)^1)*((2147483599:M)) + ((1073741824:M)^2)*((36:M)) + ((1073741824:M)^3)*((2147483623:M)) + ((1073741824:M)^3)*((48:M))) - 5*((2147483599:M) + 576) := by
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
  rw [gather503]
  rw [hwe 496 (by omega), hwe 500 (by omega), hwe 502 (by omega), hwe 503 (by omega), hwe 504 (by omega), hwo 503 (by omega)]
  change 7*w (2*503) + 5*(((1073741824:M)^1)*w (2*502) + ((1073741824:M)^2)*w (2*500) + ((1073741824:M)^3)*w (2*496) + ((1073741824:M)^3)*w (2*504)) - 5*w (2*503+1) = 7*((96:M)) + 5*(((1073741824:M)^1)*((2147483599:M)) + ((1073741824:M)^2)*((36:M)) + ((1073741824:M)^3)*((2147483623:M)) + ((1073741824:M)^3)*((48:M))) - 5*((2147483599:M) + 576)
  rw [transport_leaf_0992, transport_leaf_1000, transport_leaf_1004, transport_leaf_1006, transport_leaf_1007, transport_leaf_1008]
#print axioms pw_1006

/-- finite source-only pointWeight expansion at 1008; no field reduction --/
lemma pw_1008 : pw 1008 = 7*((48:M)) + 5*((2147483551:M) + 576) - 5*((2147483623:M) + 576) := by
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
  rw [gather504]
  rw [hwe 504 (by omega), hwe 505 (by omega), hwo 504 (by omega)]
  change 7*w (2*504) + 5*(w (2*505)) - 5*w (2*504+1) = 7*((48:M)) + 5*((2147483551:M) + 576) - 5*((2147483623:M) + 576)
  rw [transport_leaf_1008, transport_leaf_1009, transport_leaf_1010]
#print axioms pw_1008

/-- finite source-only pointWeight expansion at 1009; no field reduction --/
lemma pw_1009 : pw 1009 = -5*(((48:M)) - ((1073741824:M)*((48:M)) + (1073741824:M)*((2147483583:M) + 576))) + 7*((2147483623:M) + 576) + 5*((48:M)) := by
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
  rw [gatherGather504, gather504]
  rw [hwe 504 (by omega), hwe 506 (by omega), hwo 504 (by omega), hwo 505 (by omega)]
  change -5*(w (2*504) - ((1073741824:M)*w (2*504) + (1073741824:M)*w (2*506))) + 7*w (2*504+1) + 5*(w (2*505+1)) = -5*(((48:M)) - ((1073741824:M)*((48:M)) + (1073741824:M)*((2147483583:M) + 576))) + 7*((2147483623:M) + 576) + 5*((48:M))
  rw [transport_leaf_1008, transport_leaf_1009, transport_leaf_1011, transport_leaf_1012]
#print axioms pw_1009

/-- finite source-only pointWeight expansion at 1011; no field reduction --/
lemma pw_1011 : pw 1011 = -5*(((2147483551:M) + 576) - ((1073741824:M)*((2147483551:M) + 576) + (1073741824:M)*((128:M) + 576))) + 7*((48:M)) + 5*(((1073741824:M)^1)*((2147483623:M) + 576) + ((1073741824:M)^1)*((32:M))) := by
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
  rw [gatherGather505, gather505]
  rw [hwe 505 (by omega), hwe 507 (by omega), hwo 504 (by omega), hwo 505 (by omega), hwo 506 (by omega)]
  change -5*(w (2*505) - ((1073741824:M)*w (2*505) + (1073741824:M)*w (2*507))) + 7*w (2*505+1) + 5*(((1073741824:M)^1)*w (2*504+1) + ((1073741824:M)^1)*w (2*506+1)) = -5*(((2147483551:M) + 576) - ((1073741824:M)*((2147483551:M) + 576) + (1073741824:M)*((128:M) + 576))) + 7*((48:M)) + 5*(((1073741824:M)^1)*((2147483623:M) + 576) + ((1073741824:M)^1)*((32:M)))
  rw [transport_leaf_1009, transport_leaf_1010, transport_leaf_1011, transport_leaf_1013, transport_leaf_1014]
#print axioms pw_1011

/-- finite source-only pointWeight expansion at 1012; no field reduction --/
lemma pw_1012 : pw 1012 = 7*((2147483583:M) + 576) + 5*((128:M) + 576) - 5*((32:M)) := by
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
  rw [gather506]
  rw [hwe 506 (by omega), hwe 507 (by omega), hwo 506 (by omega)]
  change 7*w (2*506) + 5*(w (2*507)) - 5*w (2*506+1) = 7*((2147483583:M) + 576) + 5*((128:M) + 576) - 5*((32:M))
  rw [transport_leaf_1012, transport_leaf_1013, transport_leaf_1014]
#print axioms pw_1012

/-- finite source-only pointWeight expansion at 1013; no field reduction --/
lemma pw_1013 : pw 1013 = -5*(((2147483583:M) + 576) - ((1073741824:M)*((2147483583:M) + 576) + (1073741824:M)^2*((48:M)) + (1073741824:M)^2*((2147483575:M) + 576))) + 7*((32:M)) + 5*((2147483583:M)) := by
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
  rw [gatherGather506, gather506]
  rw [hwe 504 (by omega), hwe 506 (by omega), hwe 508 (by omega), hwo 506 (by omega), hwo 507 (by omega)]
  change -5*(w (2*506) - ((1073741824:M)*w (2*506) + (1073741824:M)^2*w (2*504) + (1073741824:M)^2*w (2*508))) + 7*w (2*506+1) + 5*(w (2*507+1)) = -5*(((2147483583:M) + 576) - ((1073741824:M)*((2147483583:M) + 576) + (1073741824:M)^2*((48:M)) + (1073741824:M)^2*((2147483575:M) + 576))) + 7*((32:M)) + 5*((2147483583:M))
  rw [transport_leaf_1008, transport_leaf_1012, transport_leaf_1013, transport_leaf_1015, transport_leaf_1016]
#print axioms pw_1013

/-- finite source-only pointWeight expansion at 1015; no field reduction --/
lemma pw_1015 : pw 1015 = -5*(((128:M) + 576) - ((1073741824:M)*((128:M) + 576) + (1073741824:M)^2*((2147483551:M) + 576) + (1073741824:M)^2*((144:M) + 576))) + 7*((2147483583:M)) + 5*(((1073741824:M)^1)*((32:M)) + ((1073741824:M)^2)*((2147483623:M) + 576) + ((1073741824:M)^2)*((36:M))) := by
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
  rw [gatherGather507, gather507]
  rw [hwe 505 (by omega), hwe 507 (by omega), hwe 509 (by omega), hwo 504 (by omega), hwo 506 (by omega), hwo 507 (by omega), hwo 508 (by omega)]
  change -5*(w (2*507) - ((1073741824:M)*w (2*507) + (1073741824:M)^2*w (2*505) + (1073741824:M)^2*w (2*509))) + 7*w (2*507+1) + 5*(((1073741824:M)^1)*w (2*506+1) + ((1073741824:M)^2)*w (2*504+1) + ((1073741824:M)^2)*w (2*508+1)) = -5*(((128:M) + 576) - ((1073741824:M)*((128:M) + 576) + (1073741824:M)^2*((2147483551:M) + 576) + (1073741824:M)^2*((144:M) + 576))) + 7*((2147483583:M)) + 5*(((1073741824:M)^1)*((32:M)) + ((1073741824:M)^2)*((2147483623:M) + 576) + ((1073741824:M)^2)*((36:M)))
  rw [transport_leaf_1009, transport_leaf_1010, transport_leaf_1013, transport_leaf_1014, transport_leaf_1015, transport_leaf_1017, transport_leaf_1018]
#print axioms pw_1015

/-- finite source-only pointWeight expansion at 1016; no field reduction --/
lemma pw_1016 : pw 1016 = 7*((2147483575:M) + 576) + 5*((144:M) + 576) - 5*((36:M)) := by
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
  rw [gather508]
  rw [hwe 508 (by omega), hwe 509 (by omega), hwo 508 (by omega)]
  change 7*w (2*508) + 5*(w (2*509)) - 5*w (2*508+1) = 7*((2147483575:M) + 576) + 5*((144:M) + 576) - 5*((36:M))
  rw [transport_leaf_1016, transport_leaf_1017, transport_leaf_1018]
#print axioms pw_1016

/-- finite source-only pointWeight expansion at 1017; no field reduction --/
lemma pw_1017 : pw 1017 = -5*(((2147483575:M) + 576) - ((1073741824:M)*((2147483575:M) + 576) + (1073741824:M)*((96:M) + 576))) + 7*((36:M)) + 5*((2147483575:M)) := by
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
  rw [gatherGather508, gather508]
  rw [hwe 508 (by omega), hwe 510 (by omega), hwo 508 (by omega), hwo 509 (by omega)]
  change -5*(w (2*508) - ((1073741824:M)*w (2*508) + (1073741824:M)*w (2*510))) + 7*w (2*508+1) + 5*(w (2*509+1)) = -5*(((2147483575:M) + 576) - ((1073741824:M)*((2147483575:M) + 576) + (1073741824:M)*((96:M) + 576))) + 7*((36:M)) + 5*((2147483575:M))
  rw [transport_leaf_1016, transport_leaf_1017, transport_leaf_1019, transport_leaf_1020]
#print axioms pw_1017

/-- finite source-only pointWeight expansion at 1018; no field reduction --/
lemma pw_1018 : pw 1018 = 7*((144:M) + 576) + 5*(((1073741824:M)^1)*((2147483575:M) + 576) + ((1073741824:M)^1)*((96:M) + 576)) - 5*((2147483575:M)) := by
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
  rw [gather509]
  rw [hwe 508 (by omega), hwe 509 (by omega), hwe 510 (by omega), hwo 509 (by omega)]
  change 7*w (2*509) + 5*(((1073741824:M)^1)*w (2*508) + ((1073741824:M)^1)*w (2*510)) - 5*w (2*509+1) = 7*((144:M) + 576) + 5*(((1073741824:M)^1)*((2147483575:M) + 576) + ((1073741824:M)^1)*((96:M) + 576)) - 5*((2147483575:M))
  rw [transport_leaf_1016, transport_leaf_1018, transport_leaf_1019, transport_leaf_1020]
#print axioms pw_1018

/-- finite source-only pointWeight expansion at 1019; no field reduction --/
lemma pw_1019 : pw 1019 = -5*(((144:M) + 576) - ((1073741824:M)*((144:M) + 576) + (1073741824:M)*((2147483455:M)))) + 7*((2147483575:M)) + 5*(((1073741824:M)^1)*((36:M)) + ((1073741824:M)^1)*((1152:M) + 576)) := by
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
  rw [gatherGather509, gather509]
  rw [hwe 509 (by omega), hwe 511 (by omega), hwo 508 (by omega), hwo 509 (by omega), hwo 510 (by omega)]
  change -5*(w (2*509) - ((1073741824:M)*w (2*509) + (1073741824:M)*w (2*511))) + 7*w (2*509+1) + 5*(((1073741824:M)^1)*w (2*508+1) + ((1073741824:M)^1)*w (2*510+1)) = -5*(((144:M) + 576) - ((1073741824:M)*((144:M) + 576) + (1073741824:M)*((2147483455:M)))) + 7*((2147483575:M)) + 5*(((1073741824:M)^1)*((36:M)) + ((1073741824:M)^1)*((1152:M) + 576))
  rw [transport_leaf_1017, transport_leaf_1018, transport_leaf_1019, transport_leaf_1021, transport_leaf_1022]
#print axioms pw_1019

end
end AspisV8R19.R760PointWeightChunk10
