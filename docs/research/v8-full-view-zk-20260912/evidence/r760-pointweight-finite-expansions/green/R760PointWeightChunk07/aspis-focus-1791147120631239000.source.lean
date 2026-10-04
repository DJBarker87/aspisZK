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

namespace AspisV8R19.R760PointWeightChunk07
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

/-- finite source-only pointWeight expansion at 636; no field reduction --/
lemma pw_0636 : pw 636 = 7*((288:M)) + 5*((2147483071:M)) - 5*((2147483503:M) + 576) := by
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
  rw [gather318]
  rw [hwe 318 (by omega), hwe 319 (by omega), hwo 318 (by omega)]
  change 7*w (2*318) + 5*(w (2*319)) - 5*w (2*318+1) = 7*((288:M)) + 5*((2147483071:M)) - 5*((2147483503:M) + 576)
  rw [transport_leaf_0636, transport_leaf_0637, transport_leaf_0638]
#print axioms pw_0636

/-- finite source-only pointWeight expansion at 637; no field reduction --/
lemma pw_0637 : pw 637 = -5*(((288:M)) - ((1073741824:M)*((288:M)) + (1073741824:M)^2*((2147483431:M)) + (1073741824:M)^3*((144:M) + 576) + (1073741824:M)^4*((2147483575:M) + 576) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^6*((576 : M)) + (1073741824:M)^6*((576 : M)))) + 7*((2147483503:M) + 576) + 5*((288:M)) := by
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
  rw [gatherGather318, gather318]
  rw [hwe 256 (by omega), hwe 288 (by omega), hwe 304 (by omega), hwe 312 (by omega), hwe 316 (by omega), hwe 318 (by omega), hwe 320 (by omega), hwo 318 (by omega), hwo 319 (by omega)]
  change -5*(w (2*318) - ((1073741824:M)*w (2*318) + (1073741824:M)^2*w (2*316) + (1073741824:M)^3*w (2*312) + (1073741824:M)^4*w (2*304) + (1073741824:M)^5*w (2*288) + (1073741824:M)^6*w (2*256) + (1073741824:M)^6*w (2*320))) + 7*w (2*318+1) + 5*(w (2*319+1)) = -5*(((288:M)) - ((1073741824:M)*((288:M)) + (1073741824:M)^2*((2147483431:M)) + (1073741824:M)^3*((144:M) + 576) + (1073741824:M)^4*((2147483575:M) + 576) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^6*((576 : M)) + (1073741824:M)^6*((576 : M)))) + 7*((2147483503:M) + 576) + 5*((288:M))
  rw [w_guarded_leaf_0512, w_guarded_leaf_0576, transport_leaf_0608, transport_leaf_0624, transport_leaf_0632, transport_leaf_0636, transport_leaf_0637, transport_leaf_0639, w_guarded_leaf_0640]
#print axioms pw_0637

/-- finite source-only pointWeight expansion at 638; no field reduction --/
lemma pw_0638 : pw 638 = 7*((2147483071:M)) + 5*(((1073741824:M)^1)*((288:M)) + ((1073741824:M)^2)*((2147483431:M)) + ((1073741824:M)^3)*((144:M) + 576) + ((1073741824:M)^4)*((2147483575:M) + 576) + ((1073741824:M)^5)*((576 : M)) + ((1073741824:M)^6)*((576 : M)) + ((1073741824:M)^6)*((576 : M))) - 5*((288:M)) := by
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
  rw [gather319]
  rw [hwe 256 (by omega), hwe 288 (by omega), hwe 304 (by omega), hwe 312 (by omega), hwe 316 (by omega), hwe 318 (by omega), hwe 319 (by omega), hwe 320 (by omega), hwo 319 (by omega)]
  change 7*w (2*319) + 5*(((1073741824:M)^1)*w (2*318) + ((1073741824:M)^2)*w (2*316) + ((1073741824:M)^3)*w (2*312) + ((1073741824:M)^4)*w (2*304) + ((1073741824:M)^5)*w (2*288) + ((1073741824:M)^6)*w (2*256) + ((1073741824:M)^6)*w (2*320)) - 5*w (2*319+1) = 7*((2147483071:M)) + 5*(((1073741824:M)^1)*((288:M)) + ((1073741824:M)^2)*((2147483431:M)) + ((1073741824:M)^3)*((144:M) + 576) + ((1073741824:M)^4)*((2147483575:M) + 576) + ((1073741824:M)^5)*((576 : M)) + ((1073741824:M)^6)*((576 : M)) + ((1073741824:M)^6)*((576 : M))) - 5*((288:M))
  rw [w_guarded_leaf_0512, w_guarded_leaf_0576, transport_leaf_0608, transport_leaf_0624, transport_leaf_0632, transport_leaf_0636, transport_leaf_0638, transport_leaf_0639, w_guarded_leaf_0640]
#print axioms pw_0638

/-- finite source-only pointWeight expansion at 639; no field reduction --/
lemma pw_0639 : pw 639 = -5*(((2147483071:M)) - ((1073741824:M)*((2147483071:M)) + (1073741824:M)^2*((432:M)) + (1073741824:M)^3*((2147483359:M)) + (1073741824:M)^4*((144:M) + 576) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^6*((576 : M)) + (1073741824:M)^6*((576 : M)))) + 7*((288:M)) + 5*(((1073741824:M)^1)*((2147483503:M) + 576) + ((1073741824:M)^2)*((108:M) + 576) + ((1073741824:M)^3)*((2147483575:M) + 576) + ((1073741824:M)^4)*((36:M) + 576) + ((1073741824:M)^5)*((576 : M)) + ((1073741824:M)^6)*((576 : M)) + ((1073741824:M)^6)*((576 : M))) := by
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
  rw [gatherGather319, gather319]
  rw [hwe 257 (by omega), hwe 289 (by omega), hwe 305 (by omega), hwe 313 (by omega), hwe 317 (by omega), hwe 319 (by omega), hwe 321 (by omega), hwo 256 (by omega), hwo 288 (by omega), hwo 304 (by omega), hwo 312 (by omega), hwo 316 (by omega), hwo 318 (by omega), hwo 319 (by omega), hwo 320 (by omega)]
  change -5*(w (2*319) - ((1073741824:M)*w (2*319) + (1073741824:M)^2*w (2*317) + (1073741824:M)^3*w (2*313) + (1073741824:M)^4*w (2*305) + (1073741824:M)^5*w (2*289) + (1073741824:M)^6*w (2*257) + (1073741824:M)^6*w (2*321))) + 7*w (2*319+1) + 5*(((1073741824:M)^1)*w (2*318+1) + ((1073741824:M)^2)*w (2*316+1) + ((1073741824:M)^3)*w (2*312+1) + ((1073741824:M)^4)*w (2*304+1) + ((1073741824:M)^5)*w (2*288+1) + ((1073741824:M)^6)*w (2*256+1) + ((1073741824:M)^6)*w (2*320+1)) = -5*(((2147483071:M)) - ((1073741824:M)*((2147483071:M)) + (1073741824:M)^2*((432:M)) + (1073741824:M)^3*((2147483359:M)) + (1073741824:M)^4*((144:M) + 576) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^6*((576 : M)) + (1073741824:M)^6*((576 : M)))) + 7*((288:M)) + 5*(((1073741824:M)^1)*((2147483503:M) + 576) + ((1073741824:M)^2)*((108:M) + 576) + ((1073741824:M)^3)*((2147483575:M) + 576) + ((1073741824:M)^4)*((36:M) + 576) + ((1073741824:M)^5)*((576 : M)) + ((1073741824:M)^6)*((576 : M)) + ((1073741824:M)^6)*((576 : M)))
  rw [w_guarded_leaf_0513, w_guarded_leaf_0514, w_guarded_leaf_0577, w_guarded_leaf_0578, transport_leaf_0609, transport_leaf_0610, transport_leaf_0625, transport_leaf_0626, transport_leaf_0633, transport_leaf_0634, transport_leaf_0637, transport_leaf_0638, transport_leaf_0639, w_guarded_leaf_0641, w_guarded_leaf_0642]
#print axioms pw_0639

/-- finite source-only pointWeight expansion at 752; no field reduction --/
lemma pw_0752 : pw 752 = 7*((2147483575:M) + 576) + 5*((144:M) + 576) - 5*((36:M) + 576) := by
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
  rw [gather376]
  rw [hwe 376 (by omega), hwe 377 (by omega), hwo 376 (by omega)]
  change 7*w (2*376) + 5*(w (2*377)) - 5*w (2*376+1) = 7*((2147483575:M) + 576) + 5*((144:M) + 576) - 5*((36:M) + 576)
  rw [transport_leaf_0752, transport_leaf_0753, transport_leaf_0754]
#print axioms pw_0752

/-- finite source-only pointWeight expansion at 755; no field reduction --/
lemma pw_0755 : pw 755 = -5*(((144:M) + 576) - ((1073741824:M)*((144:M) + 576) + (1073741824:M)*((2147483455:M) + 576))) + 7*((2147483575:M)) + 5*(((1073741824:M)^1)*((36:M) + 576) + ((1073741824:M)^1)*((2147483599:M))) := by
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
  rw [gatherGather377, gather377]
  rw [hwe 377 (by omega), hwe 379 (by omega), hwo 376 (by omega), hwo 377 (by omega), hwo 378 (by omega)]
  change -5*(w (2*377) - ((1073741824:M)*w (2*377) + (1073741824:M)*w (2*379))) + 7*w (2*377+1) + 5*(((1073741824:M)^1)*w (2*376+1) + ((1073741824:M)^1)*w (2*378+1)) = -5*(((144:M) + 576) - ((1073741824:M)*((144:M) + 576) + (1073741824:M)*((2147483455:M) + 576))) + 7*((2147483575:M)) + 5*(((1073741824:M)^1)*((36:M) + 576) + ((1073741824:M)^1)*((2147483599:M)))
  rw [transport_leaf_0753, transport_leaf_0754, transport_leaf_0755, transport_leaf_0757, transport_leaf_0758]
#print axioms pw_0755

/-- finite source-only pointWeight expansion at 756; no field reduction --/
lemma pw_0756 : pw 756 = 7*((96:M) + 576) + 5*((2147483455:M) + 576) - 5*((2147483599:M)) := by
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
  rw [gather378]
  rw [hwe 378 (by omega), hwe 379 (by omega), hwo 378 (by omega)]
  change 7*w (2*378) + 5*(w (2*379)) - 5*w (2*378+1) = 7*((96:M) + 576) + 5*((2147483455:M) + 576) - 5*((2147483599:M))
  rw [transport_leaf_0756, transport_leaf_0757, transport_leaf_0758]
#print axioms pw_0756

/-- finite source-only pointWeight expansion at 757; no field reduction --/
lemma pw_0757 : pw 757 = -5*(((96:M) + 576) - ((1073741824:M)*((96:M) + 576) + (1073741824:M)^2*((2147483575:M) + 576) + (1073741824:M)^2*((108:M) + 576))) + 7*((2147483599:M)) + 5*((96:M)) := by
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
  rw [gatherGather378, gather378]
  rw [hwe 376 (by omega), hwe 378 (by omega), hwe 380 (by omega), hwo 378 (by omega), hwo 379 (by omega)]
  change -5*(w (2*378) - ((1073741824:M)*w (2*378) + (1073741824:M)^2*w (2*376) + (1073741824:M)^2*w (2*380))) + 7*w (2*378+1) + 5*(w (2*379+1)) = -5*(((96:M) + 576) - ((1073741824:M)*((96:M) + 576) + (1073741824:M)^2*((2147483575:M) + 576) + (1073741824:M)^2*((108:M) + 576))) + 7*((2147483599:M)) + 5*((96:M))
  rw [transport_leaf_0752, transport_leaf_0756, transport_leaf_0757, transport_leaf_0759, transport_leaf_0760]
#print axioms pw_0757

/-- finite source-only pointWeight expansion at 759; no field reduction --/
lemma pw_0759 : pw 759 = -5*(((2147483455:M) + 576) - ((1073741824:M)*((2147483455:M) + 576) + (1073741824:M)^2*((144:M) + 576) + (1073741824:M)^2*((2147483431:M) + 576))) + 7*((96:M)) + 5*(((1073741824:M)^1)*((2147483599:M)) + ((1073741824:M)^2)*((36:M) + 576) + ((1073741824:M)^2)*((2147483593:M))) := by
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
  rw [gatherGather379, gather379]
  rw [hwe 377 (by omega), hwe 379 (by omega), hwe 381 (by omega), hwo 376 (by omega), hwo 378 (by omega), hwo 379 (by omega), hwo 380 (by omega)]
  change -5*(w (2*379) - ((1073741824:M)*w (2*379) + (1073741824:M)^2*w (2*377) + (1073741824:M)^2*w (2*381))) + 7*w (2*379+1) + 5*(((1073741824:M)^1)*w (2*378+1) + ((1073741824:M)^2)*w (2*376+1) + ((1073741824:M)^2)*w (2*380+1)) = -5*(((2147483455:M) + 576) - ((1073741824:M)*((2147483455:M) + 576) + (1073741824:M)^2*((144:M) + 576) + (1073741824:M)^2*((2147483431:M) + 576))) + 7*((96:M)) + 5*(((1073741824:M)^1)*((2147483599:M)) + ((1073741824:M)^2)*((36:M) + 576) + ((1073741824:M)^2)*((2147483593:M)))
  rw [transport_leaf_0753, transport_leaf_0754, transport_leaf_0757, transport_leaf_0758, transport_leaf_0759, transport_leaf_0761, transport_leaf_0762]
#print axioms pw_0759

/-- finite source-only pointWeight expansion at 760; no field reduction --/
lemma pw_0760 : pw 760 = 7*((108:M) + 576) + 5*((2147483431:M) + 576) - 5*((2147483593:M)) := by
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
  rw [gather380]
  rw [hwe 380 (by omega), hwe 381 (by omega), hwo 380 (by omega)]
  change 7*w (2*380) + 5*(w (2*381)) - 5*w (2*380+1) = 7*((108:M) + 576) + 5*((2147483431:M) + 576) - 5*((2147483593:M))
  rw [transport_leaf_0760, transport_leaf_0761, transport_leaf_0762]
#print axioms pw_0760

/-- finite source-only pointWeight expansion at 761; no field reduction --/
lemma pw_0761 : pw 761 = -5*(((108:M) + 576) - ((1073741824:M)*((108:M) + 576) + (1073741824:M)*((2147483503:M) + 576))) + 7*((2147483593:M)) + 5*((108:M)) := by
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
  rw [gatherGather380, gather380]
  rw [hwe 380 (by omega), hwe 382 (by omega), hwo 380 (by omega), hwo 381 (by omega)]
  change -5*(w (2*380) - ((1073741824:M)*w (2*380) + (1073741824:M)*w (2*382))) + 7*w (2*380+1) + 5*(w (2*381+1)) = -5*(((108:M) + 576) - ((1073741824:M)*((108:M) + 576) + (1073741824:M)*((2147483503:M) + 576))) + 7*((2147483593:M)) + 5*((108:M))
  rw [transport_leaf_0760, transport_leaf_0761, transport_leaf_0763, transport_leaf_0764]
#print axioms pw_0761

/-- finite source-only pointWeight expansion at 763; no field reduction --/
lemma pw_0763 : pw 763 = -5*(((2147483431:M) + 576) - ((1073741824:M)*((2147483431:M) + 576) + (1073741824:M)*((288:M)))) + 7*((108:M)) + 5*(((1073741824:M)^1)*((2147483593:M)) + ((1073741824:M)^1)*((72:M))) := by
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
  rw [gatherGather381, gather381]
  rw [hwe 381 (by omega), hwe 383 (by omega), hwo 380 (by omega), hwo 381 (by omega), hwo 382 (by omega)]
  change -5*(w (2*381) - ((1073741824:M)*w (2*381) + (1073741824:M)*w (2*383))) + 7*w (2*381+1) + 5*(((1073741824:M)^1)*w (2*380+1) + ((1073741824:M)^1)*w (2*382+1)) = -5*(((2147483431:M) + 576) - ((1073741824:M)*((2147483431:M) + 576) + (1073741824:M)*((288:M)))) + 7*((108:M)) + 5*(((1073741824:M)^1)*((2147483593:M)) + ((1073741824:M)^1)*((72:M)))
  rw [transport_leaf_0761, transport_leaf_0762, transport_leaf_0763, transport_leaf_0765, transport_leaf_0766]
#print axioms pw_0763

/-- finite source-only pointWeight expansion at 764; no field reduction --/
lemma pw_0764 : pw 764 = 7*((2147483503:M) + 576) + 5*((288:M)) - 5*((72:M)) := by
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
  rw [gather382]
  rw [hwe 382 (by omega), hwe 383 (by omega), hwo 382 (by omega)]
  change 7*w (2*382) + 5*(w (2*383)) - 5*w (2*382+1) = 7*((2147483503:M) + 576) + 5*((288:M)) - 5*((72:M))
  rw [transport_leaf_0764, transport_leaf_0765, transport_leaf_0766]
#print axioms pw_0764

/-- finite source-only pointWeight expansion at 765; no field reduction --/
lemma pw_0765 : pw 765 = -5*(((2147483503:M) + 576) - ((1073741824:M)*((2147483503:M) + 576) + (1073741824:M)^2*((108:M) + 576) + (1073741824:M)^3*((2147483575:M) + 576) + (1073741824:M)^4*((36:M) + 576) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^6*((576 : M)) + (1073741824:M)^7*((576 : M)) + (1073741824:M)^7*((576 : M)))) + 7*((72:M)) + 5*((2147483503:M) + 576) := by
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
  rw [gatherGather382, gather382]
  rw [hwe 256 (by omega), hwe 320 (by omega), hwe 352 (by omega), hwe 368 (by omega), hwe 376 (by omega), hwe 380 (by omega), hwe 382 (by omega), hwe 384 (by omega), hwo 382 (by omega), hwo 383 (by omega)]
  change -5*(w (2*382) - ((1073741824:M)*w (2*382) + (1073741824:M)^2*w (2*380) + (1073741824:M)^3*w (2*376) + (1073741824:M)^4*w (2*368) + (1073741824:M)^5*w (2*352) + (1073741824:M)^6*w (2*320) + (1073741824:M)^7*w (2*256) + (1073741824:M)^7*w (2*384))) + 7*w (2*382+1) + 5*(w (2*383+1)) = -5*(((2147483503:M) + 576) - ((1073741824:M)*((2147483503:M) + 576) + (1073741824:M)^2*((108:M) + 576) + (1073741824:M)^3*((2147483575:M) + 576) + (1073741824:M)^4*((36:M) + 576) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^6*((576 : M)) + (1073741824:M)^7*((576 : M)) + (1073741824:M)^7*((576 : M)))) + 7*((72:M)) + 5*((2147483503:M) + 576)
  rw [w_guarded_leaf_0512, w_guarded_leaf_0640, w_guarded_leaf_0704, transport_leaf_0736, transport_leaf_0752, transport_leaf_0760, transport_leaf_0764, transport_leaf_0765, transport_leaf_0767, w_guarded_leaf_0768]
#print axioms pw_0765

/-- finite source-only pointWeight expansion at 766; no field reduction --/
lemma pw_0766 : pw 766 = 7*((288:M)) + 5*(((1073741824:M)^1)*((2147483503:M) + 576) + ((1073741824:M)^2)*((108:M) + 576) + ((1073741824:M)^3)*((2147483575:M) + 576) + ((1073741824:M)^4)*((36:M) + 576) + ((1073741824:M)^5)*((576 : M)) + ((1073741824:M)^6)*((576 : M)) + ((1073741824:M)^7)*((576 : M)) + ((1073741824:M)^7)*((576 : M))) - 5*((2147483503:M) + 576) := by
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
  rw [gather383]
  rw [hwe 256 (by omega), hwe 320 (by omega), hwe 352 (by omega), hwe 368 (by omega), hwe 376 (by omega), hwe 380 (by omega), hwe 382 (by omega), hwe 383 (by omega), hwe 384 (by omega), hwo 383 (by omega)]
  change 7*w (2*383) + 5*(((1073741824:M)^1)*w (2*382) + ((1073741824:M)^2)*w (2*380) + ((1073741824:M)^3)*w (2*376) + ((1073741824:M)^4)*w (2*368) + ((1073741824:M)^5)*w (2*352) + ((1073741824:M)^6)*w (2*320) + ((1073741824:M)^7)*w (2*256) + ((1073741824:M)^7)*w (2*384)) - 5*w (2*383+1) = 7*((288:M)) + 5*(((1073741824:M)^1)*((2147483503:M) + 576) + ((1073741824:M)^2)*((108:M) + 576) + ((1073741824:M)^3)*((2147483575:M) + 576) + ((1073741824:M)^4)*((36:M) + 576) + ((1073741824:M)^5)*((576 : M)) + ((1073741824:M)^6)*((576 : M)) + ((1073741824:M)^7)*((576 : M)) + ((1073741824:M)^7)*((576 : M))) - 5*((2147483503:M) + 576)
  rw [w_guarded_leaf_0512, w_guarded_leaf_0640, w_guarded_leaf_0704, transport_leaf_0736, transport_leaf_0752, transport_leaf_0760, transport_leaf_0764, transport_leaf_0766, transport_leaf_0767, w_guarded_leaf_0768]
#print axioms pw_0766

/-- finite source-only pointWeight expansion at 880; no field reduction --/
lemma pw_0880 : pw 880 = 7*((2147483551:M) + 576) + 5*((192:M)) - 5*((48:M) + 576) := by
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
  rw [gather440]
  rw [hwe 440 (by omega), hwe 441 (by omega), hwo 440 (by omega)]
  change 7*w (2*440) + 5*(w (2*441)) - 5*w (2*440+1) = 7*((2147483551:M) + 576) + 5*((192:M)) - 5*((48:M) + 576)
  rw [transport_leaf_0880, transport_leaf_0881, transport_leaf_0882]
#print axioms pw_0880

/-- finite source-only pointWeight expansion at 882; no field reduction --/
lemma pw_0882 : pw 882 = 7*((192:M)) + 5*(((1073741824:M)^1)*((2147483551:M) + 576) + ((1073741824:M)^1)*((128:M))) - 5*((2147483551:M) + 576) := by
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
  rw [gather441]
  rw [hwe 440 (by omega), hwe 441 (by omega), hwe 442 (by omega), hwo 441 (by omega)]
  change 7*w (2*441) + 5*(((1073741824:M)^1)*w (2*440) + ((1073741824:M)^1)*w (2*442)) - 5*w (2*441+1) = 7*((192:M)) + 5*(((1073741824:M)^1)*((2147483551:M) + 576) + ((1073741824:M)^1)*((128:M))) - 5*((2147483551:M) + 576)
  rw [transport_leaf_0880, transport_leaf_0882, transport_leaf_0883, transport_leaf_0884]
#print axioms pw_0882

/-- finite source-only pointWeight expansion at 884; no field reduction --/
lemma pw_0884 : pw 884 = 7*((128:M)) + 5*((2147483391:M)) - 5*((2147483583:M) + 576) := by
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
  rw [gather442]
  rw [hwe 442 (by omega), hwe 443 (by omega), hwo 442 (by omega)]
  change 7*w (2*442) + 5*(w (2*443)) - 5*w (2*442+1) = 7*((128:M)) + 5*((2147483391:M)) - 5*((2147483583:M) + 576)
  rw [transport_leaf_0884, transport_leaf_0885, transport_leaf_0886]
#print axioms pw_0884

/-- finite source-only pointWeight expansion at 885; no field reduction --/
lemma pw_0885 : pw 885 = -5*(((128:M)) - ((1073741824:M)*((128:M)) + (1073741824:M)^2*((2147483551:M) + 576) + (1073741824:M)^2*((144:M)))) + 7*((2147483583:M) + 576) + 5*((128:M) + 576) := by
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
  rw [gatherGather442, gather442]
  rw [hwe 440 (by omega), hwe 442 (by omega), hwe 444 (by omega), hwo 442 (by omega), hwo 443 (by omega)]
  change -5*(w (2*442) - ((1073741824:M)*w (2*442) + (1073741824:M)^2*w (2*440) + (1073741824:M)^2*w (2*444))) + 7*w (2*442+1) + 5*(w (2*443+1)) = -5*(((128:M)) - ((1073741824:M)*((128:M)) + (1073741824:M)^2*((2147483551:M) + 576) + (1073741824:M)^2*((144:M)))) + 7*((2147483583:M) + 576) + 5*((128:M) + 576)
  rw [transport_leaf_0880, transport_leaf_0884, transport_leaf_0885, transport_leaf_0887, transport_leaf_0888]
#print axioms pw_0885

/-- finite source-only pointWeight expansion at 886; no field reduction --/
lemma pw_0886 : pw 886 = 7*((2147483391:M)) + 5*(((1073741824:M)^1)*((128:M)) + ((1073741824:M)^2)*((2147483551:M) + 576) + ((1073741824:M)^2)*((144:M))) - 5*((128:M) + 576) := by
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
  rw [gather443]
  rw [hwe 440 (by omega), hwe 442 (by omega), hwe 443 (by omega), hwe 444 (by omega), hwo 443 (by omega)]
  change 7*w (2*443) + 5*(((1073741824:M)^1)*w (2*442) + ((1073741824:M)^2)*w (2*440) + ((1073741824:M)^2)*w (2*444)) - 5*w (2*443+1) = 7*((2147483391:M)) + 5*(((1073741824:M)^1)*((128:M)) + ((1073741824:M)^2)*((2147483551:M) + 576) + ((1073741824:M)^2)*((144:M))) - 5*((128:M) + 576)
  rw [transport_leaf_0880, transport_leaf_0884, transport_leaf_0886, transport_leaf_0887, transport_leaf_0888]
#print axioms pw_0886

/-- finite source-only pointWeight expansion at 888; no field reduction --/
lemma pw_0888 : pw 888 = 7*((144:M)) + 5*((2147483359:M)) - 5*((2147483575:M) + 576) := by
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
  rw [gather444]
  rw [hwe 444 (by omega), hwe 445 (by omega), hwo 444 (by omega)]
  change 7*w (2*444) + 5*(w (2*445)) - 5*w (2*444+1) = 7*((144:M)) + 5*((2147483359:M)) - 5*((2147483575:M) + 576)
  rw [transport_leaf_0888, transport_leaf_0889, transport_leaf_0890]
#print axioms pw_0888

/-- finite source-only pointWeight expansion at 889; no field reduction --/
lemma pw_0889 : pw 889 = -5*(((144:M)) - ((1073741824:M)*((144:M)) + (1073741824:M)*((2147483455:M)))) + 7*((2147483575:M) + 576) + 5*((144:M) + 576) := by
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
  rw [gatherGather444, gather444]
  rw [hwe 444 (by omega), hwe 446 (by omega), hwo 444 (by omega), hwo 445 (by omega)]
  change -5*(w (2*444) - ((1073741824:M)*w (2*444) + (1073741824:M)*w (2*446))) + 7*w (2*444+1) + 5*(w (2*445+1)) = -5*(((144:M)) - ((1073741824:M)*((144:M)) + (1073741824:M)*((2147483455:M)))) + 7*((2147483575:M) + 576) + 5*((144:M) + 576)
  rw [transport_leaf_0888, transport_leaf_0889, transport_leaf_0891, transport_leaf_0892]
#print axioms pw_0889

/-- finite source-only pointWeight expansion at 890; no field reduction --/
lemma pw_0890 : pw 890 = 7*((2147483359:M)) + 5*(((1073741824:M)^1)*((144:M)) + ((1073741824:M)^1)*((2147483455:M))) - 5*((144:M) + 576) := by
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
  rw [gather445]
  rw [hwe 444 (by omega), hwe 445 (by omega), hwe 446 (by omega), hwo 445 (by omega)]
  change 7*w (2*445) + 5*(((1073741824:M)^1)*w (2*444) + ((1073741824:M)^1)*w (2*446)) - 5*w (2*445+1) = 7*((2147483359:M)) + 5*(((1073741824:M)^1)*((144:M)) + ((1073741824:M)^1)*((2147483455:M))) - 5*((144:M) + 576)
  rw [transport_leaf_0888, transport_leaf_0890, transport_leaf_0891, transport_leaf_0892]
#print axioms pw_0890

/-- finite source-only pointWeight expansion at 892; no field reduction --/
lemma pw_0892 : pw 892 = 7*((2147483455:M)) + 5*((384:M)) - 5*((96:M) + 576) := by
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
  rw [gather446]
  rw [hwe 446 (by omega), hwe 447 (by omega), hwo 446 (by omega)]
  change 7*w (2*446) + 5*(w (2*447)) - 5*w (2*446+1) = 7*((2147483455:M)) + 5*((384:M)) - 5*((96:M) + 576)
  rw [transport_leaf_0892, transport_leaf_0893, transport_leaf_0894]
#print axioms pw_0892

/-- finite source-only pointWeight expansion at 893; no field reduction --/
lemma pw_0893 : pw 893 = -5*(((2147483455:M)) - ((1073741824:M)*((2147483455:M)) + (1073741824:M)^2*((144:M)) + (1073741824:M)^3*((2147483551:M) + 576) + (1073741824:M)^4*((48:M) + 576) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^6*((576 : M)) + (1073741824:M)^6*((576 : M)))) + 7*((96:M) + 576) + 5*((2147483455:M) + 576) := by
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
  rw [gatherGather446, gather446]
  rw [hwe 384 (by omega), hwe 416 (by omega), hwe 432 (by omega), hwe 440 (by omega), hwe 444 (by omega), hwe 446 (by omega), hwe 448 (by omega), hwo 446 (by omega), hwo 447 (by omega)]
  change -5*(w (2*446) - ((1073741824:M)*w (2*446) + (1073741824:M)^2*w (2*444) + (1073741824:M)^3*w (2*440) + (1073741824:M)^4*w (2*432) + (1073741824:M)^5*w (2*416) + (1073741824:M)^6*w (2*384) + (1073741824:M)^6*w (2*448))) + 7*w (2*446+1) + 5*(w (2*447+1)) = -5*(((2147483455:M)) - ((1073741824:M)*((2147483455:M)) + (1073741824:M)^2*((144:M)) + (1073741824:M)^3*((2147483551:M) + 576) + (1073741824:M)^4*((48:M) + 576) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^6*((576 : M)) + (1073741824:M)^6*((576 : M)))) + 7*((96:M) + 576) + 5*((2147483455:M) + 576)
  rw [w_guarded_leaf_0768, w_guarded_leaf_0832, transport_leaf_0864, transport_leaf_0880, transport_leaf_0888, transport_leaf_0892, transport_leaf_0893, transport_leaf_0895, w_guarded_leaf_0896]
#print axioms pw_0893

/-- finite source-only pointWeight expansion at 894; no field reduction --/
lemma pw_0894 : pw 894 = 7*((384:M)) + 5*(((1073741824:M)^1)*((2147483455:M)) + ((1073741824:M)^2)*((144:M)) + ((1073741824:M)^3)*((2147483551:M) + 576) + ((1073741824:M)^4)*((48:M) + 576) + ((1073741824:M)^5)*((576 : M)) + ((1073741824:M)^6)*((576 : M)) + ((1073741824:M)^6)*((576 : M))) - 5*((2147483455:M) + 576) := by
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
  rw [gather447]
  rw [hwe 384 (by omega), hwe 416 (by omega), hwe 432 (by omega), hwe 440 (by omega), hwe 444 (by omega), hwe 446 (by omega), hwe 447 (by omega), hwe 448 (by omega), hwo 447 (by omega)]
  change 7*w (2*447) + 5*(((1073741824:M)^1)*w (2*446) + ((1073741824:M)^2)*w (2*444) + ((1073741824:M)^3)*w (2*440) + ((1073741824:M)^4)*w (2*432) + ((1073741824:M)^5)*w (2*416) + ((1073741824:M)^6)*w (2*384) + ((1073741824:M)^6)*w (2*448)) - 5*w (2*447+1) = 7*((384:M)) + 5*(((1073741824:M)^1)*((2147483455:M)) + ((1073741824:M)^2)*((144:M)) + ((1073741824:M)^3)*((2147483551:M) + 576) + ((1073741824:M)^4)*((48:M) + 576) + ((1073741824:M)^5)*((576 : M)) + ((1073741824:M)^6)*((576 : M)) + ((1073741824:M)^6)*((576 : M))) - 5*((2147483455:M) + 576)
  rw [w_guarded_leaf_0768, w_guarded_leaf_0832, transport_leaf_0864, transport_leaf_0880, transport_leaf_0888, transport_leaf_0892, transport_leaf_0894, transport_leaf_0895, w_guarded_leaf_0896]
#print axioms pw_0894

/-- finite source-only pointWeight expansion at 900; no field reduction --/
lemma pw_0900 : pw 900 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather450]
  rw [hwe 450 (by omega), hwe 451 (by omega), hwo 450 (by omega)]
  change 7*w (2*450) + 5*(w (2*451)) - 5*w (2*450+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0900, w_guarded_leaf_0901, w_guarded_leaf_0902]
#print axioms pw_0900

/-- finite source-only pointWeight expansion at 901; no field reduction --/
lemma pw_0901 : pw 901 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather450, gather450]
  rw [hwe 448 (by omega), hwe 450 (by omega), hwe 452 (by omega), hwo 450 (by omega), hwo 451 (by omega)]
  change -5*(w (2*450) - ((1073741824:M)*w (2*450) + (1073741824:M)^2*w (2*448) + (1073741824:M)^2*w (2*452))) + 7*w (2*450+1) + 5*(w (2*451+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0896, w_guarded_leaf_0900, w_guarded_leaf_0901, w_guarded_leaf_0903, w_guarded_leaf_0904]
#print axioms pw_0901

/-- finite source-only pointWeight expansion at 902; no field reduction --/
lemma pw_0902 : pw 902 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((576 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather451]
  rw [hwe 448 (by omega), hwe 450 (by omega), hwe 451 (by omega), hwe 452 (by omega), hwo 451 (by omega)]
  change 7*w (2*451) + 5*(((1073741824:M)^1)*w (2*450) + ((1073741824:M)^2)*w (2*448) + ((1073741824:M)^2)*w (2*452)) - 5*w (2*451+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((576 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0896, w_guarded_leaf_0900, w_guarded_leaf_0902, w_guarded_leaf_0903, w_guarded_leaf_0904]
#print axioms pw_0902

/-- finite source-only pointWeight expansion at 904; no field reduction --/
lemma pw_0904 : pw 904 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather452]
  rw [hwe 452 (by omega), hwe 453 (by omega), hwo 452 (by omega)]
  change 7*w (2*452) + 5*(w (2*453)) - 5*w (2*452+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0904, w_guarded_leaf_0905, w_guarded_leaf_0906]
#print axioms pw_0904

/-- finite source-only pointWeight expansion at 905; no field reduction --/
lemma pw_0905 : pw 905 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather452, gather452]
  rw [hwe 452 (by omega), hwe 454 (by omega), hwo 452 (by omega), hwo 453 (by omega)]
  change -5*(w (2*452) - ((1073741824:M)*w (2*452) + (1073741824:M)*w (2*454))) + 7*w (2*452+1) + 5*(w (2*453+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0904, w_guarded_leaf_0905, w_guarded_leaf_0907, w_guarded_leaf_0908]
#print axioms pw_0905

/-- finite source-only pointWeight expansion at 906; no field reduction --/
lemma pw_0906 : pw 906 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather453]
  rw [hwe 452 (by omega), hwe 453 (by omega), hwe 454 (by omega), hwo 453 (by omega)]
  change 7*w (2*453) + 5*(((1073741824:M)^1)*w (2*452) + ((1073741824:M)^1)*w (2*454)) - 5*w (2*453+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0904, w_guarded_leaf_0906, w_guarded_leaf_0907, w_guarded_leaf_0908]
#print axioms pw_0906

end
end AspisV8R19.R760PointWeightChunk07
