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

namespace AspisV8R19.R760PointWeightChunk09
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

/-- finite source-only pointWeight expansion at 953; no field reduction --/
lemma pw_0953 : pw 953 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((576 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather476, gather476]
  rw [hwe 476 (by omega), hwe 478 (by omega), hwo 476 (by omega), hwo 477 (by omega)]
  change -5*(w (2*476) - ((1073741824:M)*w (2*476) + (1073741824:M)*w (2*478))) + 7*w (2*476+1) + 5*(w (2*477+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((576 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0952, w_guarded_leaf_0953, w_guarded_leaf_0955, w_guarded_leaf_0956]
#print axioms pw_0953

/-- finite source-only pointWeight expansion at 954; no field reduction --/
lemma pw_0954 : pw 954 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((576 : M))) - 5*((576 : M)) := by
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
  rw [gather477]
  rw [hwe 476 (by omega), hwe 477 (by omega), hwe 478 (by omega), hwo 477 (by omega)]
  change 7*w (2*477) + 5*(((1073741824:M)^1)*w (2*476) + ((1073741824:M)^1)*w (2*478)) - 5*w (2*477+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((576 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0952, w_guarded_leaf_0954, w_guarded_leaf_0955, w_guarded_leaf_0956]
#print axioms pw_0954

/-- finite source-only pointWeight expansion at 956; no field reduction --/
lemma pw_0956 : pw 956 = 7*((576 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather478]
  rw [hwe 478 (by omega), hwe 479 (by omega), hwo 478 (by omega)]
  change 7*w (2*478) + 5*(w (2*479)) - 5*w (2*478+1) = 7*((576 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0956, w_guarded_leaf_0957, w_guarded_leaf_0958]
#print axioms pw_0956

/-- finite source-only pointWeight expansion at 958; no field reduction --/
lemma pw_0958 : pw 958 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((576 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^4)*((0 : M)) + ((1073741824:M)^5)*((576 : M)) + ((1073741824:M)^5)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather479]
  rw [hwe 448 (by omega), hwe 464 (by omega), hwe 472 (by omega), hwe 476 (by omega), hwe 478 (by omega), hwe 479 (by omega), hwe 480 (by omega), hwo 479 (by omega)]
  change 7*w (2*479) + 5*(((1073741824:M)^1)*w (2*478) + ((1073741824:M)^2)*w (2*476) + ((1073741824:M)^3)*w (2*472) + ((1073741824:M)^4)*w (2*464) + ((1073741824:M)^5)*w (2*448) + ((1073741824:M)^5)*w (2*480)) - 5*w (2*479+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((576 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^4)*((0 : M)) + ((1073741824:M)^5)*((576 : M)) + ((1073741824:M)^5)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0896, w_guarded_leaf_0928, w_guarded_leaf_0944, w_guarded_leaf_0952, w_guarded_leaf_0956, w_guarded_leaf_0958, w_guarded_leaf_0959, w_guarded_leaf_0960]
#print axioms pw_0958

/-- finite source-only pointWeight expansion at 960; no field reduction --/
lemma pw_0960 : pw 960 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather480]
  rw [hwe 480 (by omega), hwe 481 (by omega), hwo 480 (by omega)]
  change 7*w (2*480) + 5*(w (2*481)) - 5*w (2*480+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0960, w_guarded_leaf_0961, w_guarded_leaf_0962]
#print axioms pw_0960

/-- finite source-only pointWeight expansion at 961; no field reduction --/
lemma pw_0961 : pw 961 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather480, gather480]
  rw [hwe 480 (by omega), hwe 482 (by omega), hwo 480 (by omega), hwo 481 (by omega)]
  change -5*(w (2*480) - ((1073741824:M)*w (2*480) + (1073741824:M)*w (2*482))) + 7*w (2*480+1) + 5*(w (2*481+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0960, w_guarded_leaf_0961, w_guarded_leaf_0963, w_guarded_leaf_0964]
#print axioms pw_0961

/-- finite source-only pointWeight expansion at 962; no field reduction --/
lemma pw_0962 : pw 962 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather481]
  rw [hwe 480 (by omega), hwe 481 (by omega), hwe 482 (by omega), hwo 481 (by omega)]
  change 7*w (2*481) + 5*(((1073741824:M)^1)*w (2*480) + ((1073741824:M)^1)*w (2*482)) - 5*w (2*481+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0960, w_guarded_leaf_0962, w_guarded_leaf_0963, w_guarded_leaf_0964]
#print axioms pw_0962

/-- finite source-only pointWeight expansion at 964; no field reduction --/
lemma pw_0964 : pw 964 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather482]
  rw [hwe 482 (by omega), hwe 483 (by omega), hwo 482 (by omega)]
  change 7*w (2*482) + 5*(w (2*483)) - 5*w (2*482+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0964, w_guarded_leaf_0965, w_guarded_leaf_0966]
#print axioms pw_0964

/-- finite source-only pointWeight expansion at 965; no field reduction --/
lemma pw_0965 : pw 965 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather482, gather482]
  rw [hwe 480 (by omega), hwe 482 (by omega), hwe 484 (by omega), hwo 482 (by omega), hwo 483 (by omega)]
  change -5*(w (2*482) - ((1073741824:M)*w (2*482) + (1073741824:M)^2*w (2*480) + (1073741824:M)^2*w (2*484))) + 7*w (2*482+1) + 5*(w (2*483+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0960, w_guarded_leaf_0964, w_guarded_leaf_0965, w_guarded_leaf_0967, w_guarded_leaf_0968]
#print axioms pw_0965

/-- finite source-only pointWeight expansion at 966; no field reduction --/
lemma pw_0966 : pw 966 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather483]
  rw [hwe 480 (by omega), hwe 482 (by omega), hwe 483 (by omega), hwe 484 (by omega), hwo 483 (by omega)]
  change 7*w (2*483) + 5*(((1073741824:M)^1)*w (2*482) + ((1073741824:M)^2)*w (2*480) + ((1073741824:M)^2)*w (2*484)) - 5*w (2*483+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0960, w_guarded_leaf_0964, w_guarded_leaf_0966, w_guarded_leaf_0967, w_guarded_leaf_0968]
#print axioms pw_0966

/-- finite source-only pointWeight expansion at 968; no field reduction --/
lemma pw_0968 : pw 968 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather484]
  rw [hwe 484 (by omega), hwe 485 (by omega), hwo 484 (by omega)]
  change 7*w (2*484) + 5*(w (2*485)) - 5*w (2*484+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0968, w_guarded_leaf_0969, w_guarded_leaf_0970]
#print axioms pw_0968

/-- finite source-only pointWeight expansion at 969; no field reduction --/
lemma pw_0969 : pw 969 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather484, gather484]
  rw [hwe 484 (by omega), hwe 486 (by omega), hwo 484 (by omega), hwo 485 (by omega)]
  change -5*(w (2*484) - ((1073741824:M)*w (2*484) + (1073741824:M)*w (2*486))) + 7*w (2*484+1) + 5*(w (2*485+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0968, w_guarded_leaf_0969, w_guarded_leaf_0971, w_guarded_leaf_0972]
#print axioms pw_0969

/-- finite source-only pointWeight expansion at 970; no field reduction --/
lemma pw_0970 : pw 970 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather485]
  rw [hwe 484 (by omega), hwe 485 (by omega), hwe 486 (by omega), hwo 485 (by omega)]
  change 7*w (2*485) + 5*(((1073741824:M)^1)*w (2*484) + ((1073741824:M)^1)*w (2*486)) - 5*w (2*485+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0968, w_guarded_leaf_0970, w_guarded_leaf_0971, w_guarded_leaf_0972]
#print axioms pw_0970

/-- finite source-only pointWeight expansion at 972; no field reduction --/
lemma pw_0972 : pw 972 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather486]
  rw [hwe 486 (by omega), hwe 487 (by omega), hwo 486 (by omega)]
  change 7*w (2*486) + 5*(w (2*487)) - 5*w (2*486+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0972, w_guarded_leaf_0973, w_guarded_leaf_0974]
#print axioms pw_0972

/-- finite source-only pointWeight expansion at 973; no field reduction --/
lemma pw_0973 : pw 973 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((0 : M)) + (1073741824:M)^3*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather486, gather486]
  rw [hwe 480 (by omega), hwe 484 (by omega), hwe 486 (by omega), hwe 488 (by omega), hwo 486 (by omega), hwo 487 (by omega)]
  change -5*(w (2*486) - ((1073741824:M)*w (2*486) + (1073741824:M)^2*w (2*484) + (1073741824:M)^3*w (2*480) + (1073741824:M)^3*w (2*488))) + 7*w (2*486+1) + 5*(w (2*487+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((0 : M)) + (1073741824:M)^3*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0960, w_guarded_leaf_0968, w_guarded_leaf_0972, w_guarded_leaf_0973, w_guarded_leaf_0975, w_guarded_leaf_0976]
#print axioms pw_0973

/-- finite source-only pointWeight expansion at 974; no field reduction --/
lemma pw_0974 : pw 974 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^3)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather487]
  rw [hwe 480 (by omega), hwe 484 (by omega), hwe 486 (by omega), hwe 487 (by omega), hwe 488 (by omega), hwo 487 (by omega)]
  change 7*w (2*487) + 5*(((1073741824:M)^1)*w (2*486) + ((1073741824:M)^2)*w (2*484) + ((1073741824:M)^3)*w (2*480) + ((1073741824:M)^3)*w (2*488)) - 5*w (2*487+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^3)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0960, w_guarded_leaf_0968, w_guarded_leaf_0972, w_guarded_leaf_0974, w_guarded_leaf_0975, w_guarded_leaf_0976]
#print axioms pw_0974

/-- finite source-only pointWeight expansion at 976; no field reduction --/
lemma pw_0976 : pw 976 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather488]
  rw [hwe 488 (by omega), hwe 489 (by omega), hwo 488 (by omega)]
  change 7*w (2*488) + 5*(w (2*489)) - 5*w (2*488+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0976, w_guarded_leaf_0977, w_guarded_leaf_0978]
#print axioms pw_0976

/-- finite source-only pointWeight expansion at 977; no field reduction --/
lemma pw_0977 : pw 977 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather488, gather488]
  rw [hwe 488 (by omega), hwe 490 (by omega), hwo 488 (by omega), hwo 489 (by omega)]
  change -5*(w (2*488) - ((1073741824:M)*w (2*488) + (1073741824:M)*w (2*490))) + 7*w (2*488+1) + 5*(w (2*489+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0976, w_guarded_leaf_0977, w_guarded_leaf_0979, w_guarded_leaf_0980]
#print axioms pw_0977

/-- finite source-only pointWeight expansion at 978; no field reduction --/
lemma pw_0978 : pw 978 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather489]
  rw [hwe 488 (by omega), hwe 489 (by omega), hwe 490 (by omega), hwo 489 (by omega)]
  change 7*w (2*489) + 5*(((1073741824:M)^1)*w (2*488) + ((1073741824:M)^1)*w (2*490)) - 5*w (2*489+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0976, w_guarded_leaf_0978, w_guarded_leaf_0979, w_guarded_leaf_0980]
#print axioms pw_0978

/-- finite source-only pointWeight expansion at 980; no field reduction --/
lemma pw_0980 : pw 980 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather490]
  rw [hwe 490 (by omega), hwe 491 (by omega), hwo 490 (by omega)]
  change 7*w (2*490) + 5*(w (2*491)) - 5*w (2*490+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0980, w_guarded_leaf_0981, w_guarded_leaf_0982]
#print axioms pw_0980

/-- finite source-only pointWeight expansion at 981; no field reduction --/
lemma pw_0981 : pw 981 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather490, gather490]
  rw [hwe 488 (by omega), hwe 490 (by omega), hwe 492 (by omega), hwo 490 (by omega), hwo 491 (by omega)]
  change -5*(w (2*490) - ((1073741824:M)*w (2*490) + (1073741824:M)^2*w (2*488) + (1073741824:M)^2*w (2*492))) + 7*w (2*490+1) + 5*(w (2*491+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^2*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0976, w_guarded_leaf_0980, w_guarded_leaf_0981, w_guarded_leaf_0983, w_guarded_leaf_0984]
#print axioms pw_0981

/-- finite source-only pointWeight expansion at 982; no field reduction --/
lemma pw_0982 : pw 982 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather491]
  rw [hwe 488 (by omega), hwe 490 (by omega), hwe 491 (by omega), hwe 492 (by omega), hwo 491 (by omega)]
  change 7*w (2*491) + 5*(((1073741824:M)^1)*w (2*490) + ((1073741824:M)^2)*w (2*488) + ((1073741824:M)^2)*w (2*492)) - 5*w (2*491+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0976, w_guarded_leaf_0980, w_guarded_leaf_0982, w_guarded_leaf_0983, w_guarded_leaf_0984]
#print axioms pw_0982

/-- finite source-only pointWeight expansion at 984; no field reduction --/
lemma pw_0984 : pw 984 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather492]
  rw [hwe 492 (by omega), hwe 493 (by omega), hwo 492 (by omega)]
  change 7*w (2*492) + 5*(w (2*493)) - 5*w (2*492+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0984, w_guarded_leaf_0985, w_guarded_leaf_0986]
#print axioms pw_0984

/-- finite source-only pointWeight expansion at 985; no field reduction --/
lemma pw_0985 : pw 985 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather492, gather492]
  rw [hwe 492 (by omega), hwe 494 (by omega), hwo 492 (by omega), hwo 493 (by omega)]
  change -5*(w (2*492) - ((1073741824:M)*w (2*492) + (1073741824:M)*w (2*494))) + 7*w (2*492+1) + 5*(w (2*493+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)*((0 : M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0984, w_guarded_leaf_0985, w_guarded_leaf_0987, w_guarded_leaf_0988]
#print axioms pw_0985

/-- finite source-only pointWeight expansion at 986; no field reduction --/
lemma pw_0986 : pw 986 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M)) := by
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
  rw [gather493]
  rw [hwe 492 (by omega), hwe 493 (by omega), hwe 494 (by omega), hwo 493 (by omega)]
  change 7*w (2*493) + 5*(((1073741824:M)^1)*w (2*492) + ((1073741824:M)^1)*w (2*494)) - 5*w (2*493+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) - 5*((576 : M))
  rw [w_guarded_leaf_0984, w_guarded_leaf_0986, w_guarded_leaf_0987, w_guarded_leaf_0988]
#print axioms pw_0986

/-- finite source-only pointWeight expansion at 988; no field reduction --/
lemma pw_0988 : pw 988 = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M)) := by
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
  rw [gather494]
  rw [hwe 494 (by omega), hwe 495 (by omega), hwo 494 (by omega)]
  change 7*w (2*494) + 5*(w (2*495)) - 5*w (2*494+1) = 7*((0 : M)) + 5*((0 : M)) - 5*((576 : M))
  rw [w_guarded_leaf_0988, w_guarded_leaf_0989, w_guarded_leaf_0990]
#print axioms pw_0988

/-- finite source-only pointWeight expansion at 989; no field reduction --/
lemma pw_0989 : pw 989 = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((0 : M)) + (1073741824:M)^4*((0 : M)) + (1073741824:M)^4*((2147483623:M)))) + 7*((576 : M)) + 5*((576 : M)) := by
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
  rw [gatherGather494, gather494]
  rw [hwe 480 (by omega), hwe 488 (by omega), hwe 492 (by omega), hwe 494 (by omega), hwe 496 (by omega), hwo 494 (by omega), hwo 495 (by omega)]
  change -5*(w (2*494) - ((1073741824:M)*w (2*494) + (1073741824:M)^2*w (2*492) + (1073741824:M)^3*w (2*488) + (1073741824:M)^4*w (2*480) + (1073741824:M)^4*w (2*496))) + 7*w (2*494+1) + 5*(w (2*495+1)) = -5*(((0 : M)) - ((1073741824:M)*((0 : M)) + (1073741824:M)^2*((0 : M)) + (1073741824:M)^3*((0 : M)) + (1073741824:M)^4*((0 : M)) + (1073741824:M)^4*((2147483623:M)))) + 7*((576 : M)) + 5*((576 : M))
  rw [w_guarded_leaf_0960, w_guarded_leaf_0976, w_guarded_leaf_0984, w_guarded_leaf_0988, w_guarded_leaf_0989, w_guarded_leaf_0991, transport_leaf_0992]
#print axioms pw_0989

/-- finite source-only pointWeight expansion at 990; no field reduction --/
lemma pw_0990 : pw 990 = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^4)*((0 : M)) + ((1073741824:M)^4)*((2147483623:M))) - 5*((576 : M)) := by
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
  rw [gather495]
  rw [hwe 480 (by omega), hwe 488 (by omega), hwe 492 (by omega), hwe 494 (by omega), hwe 495 (by omega), hwe 496 (by omega), hwo 495 (by omega)]
  change 7*w (2*495) + 5*(((1073741824:M)^1)*w (2*494) + ((1073741824:M)^2)*w (2*492) + ((1073741824:M)^3)*w (2*488) + ((1073741824:M)^4)*w (2*480) + ((1073741824:M)^4)*w (2*496)) - 5*w (2*495+1) = 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^4)*((0 : M)) + ((1073741824:M)^4)*((2147483623:M))) - 5*((576 : M))
  rw [w_guarded_leaf_0960, w_guarded_leaf_0976, w_guarded_leaf_0984, w_guarded_leaf_0988, w_guarded_leaf_0990, w_guarded_leaf_0991, transport_leaf_0992]
#print axioms pw_0990

/-- finite source-only pointWeight expansion at 992; no field reduction --/
lemma pw_0992 : pw 992 = 7*((2147483623:M)) + 5*((48:M)) - 5*((12:M) + 576) := by
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
  rw [gather496]
  rw [hwe 496 (by omega), hwe 497 (by omega), hwo 496 (by omega)]
  change 7*w (2*496) + 5*(w (2*497)) - 5*w (2*496+1) = 7*((2147483623:M)) + 5*((48:M)) - 5*((12:M) + 576)
  rw [transport_leaf_0992, transport_leaf_0993, transport_leaf_0994]
#print axioms pw_0992

/-- finite source-only pointWeight expansion at 993; no field reduction --/
lemma pw_0993 : pw 993 = -5*(((2147483623:M)) - ((1073741824:M)*((2147483623:M)) + (1073741824:M)*((32:M)))) + 7*((12:M) + 576) + 5*((2147483623:M) + 576) := by
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
  rw [gatherGather496, gather496]
  rw [hwe 496 (by omega), hwe 498 (by omega), hwo 496 (by omega), hwo 497 (by omega)]
  change -5*(w (2*496) - ((1073741824:M)*w (2*496) + (1073741824:M)*w (2*498))) + 7*w (2*496+1) + 5*(w (2*497+1)) = -5*(((2147483623:M)) - ((1073741824:M)*((2147483623:M)) + (1073741824:M)*((32:M)))) + 7*((12:M) + 576) + 5*((2147483623:M) + 576)
  rw [transport_leaf_0992, transport_leaf_0993, transport_leaf_0995, transport_leaf_0996]
#print axioms pw_0993

/-- finite source-only pointWeight expansion at 994; no field reduction --/
lemma pw_0994 : pw 994 = 7*((48:M)) + 5*(((1073741824:M)^1)*((2147483623:M)) + ((1073741824:M)^1)*((32:M))) - 5*((2147483623:M) + 576) := by
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
  rw [gather497]
  rw [hwe 496 (by omega), hwe 497 (by omega), hwe 498 (by omega), hwo 497 (by omega)]
  change 7*w (2*497) + 5*(((1073741824:M)^1)*w (2*496) + ((1073741824:M)^1)*w (2*498)) - 5*w (2*497+1) = 7*((48:M)) + 5*(((1073741824:M)^1)*((2147483623:M)) + ((1073741824:M)^1)*((32:M))) - 5*((2147483623:M) + 576)
  rw [transport_leaf_0992, transport_leaf_0994, transport_leaf_0995, transport_leaf_0996]
#print axioms pw_0994

/-- finite source-only pointWeight expansion at 996; no field reduction --/
lemma pw_0996 : pw 996 = 7*((32:M)) + 5*((2147483583:M)) - 5*((2147483631:M) + 576) := by
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
  rw [gather498]
  rw [hwe 498 (by omega), hwe 499 (by omega), hwo 498 (by omega)]
  change 7*w (2*498) + 5*(w (2*499)) - 5*w (2*498+1) = 7*((32:M)) + 5*((2147483583:M)) - 5*((2147483631:M) + 576)
  rw [transport_leaf_0996, transport_leaf_0997, transport_leaf_0998]
#print axioms pw_0996

end
end AspisV8R19.R760PointWeightChunk09
