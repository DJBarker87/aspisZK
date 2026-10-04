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

namespace AspisV8R19.R760PointWeightChunk05
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

/-- finite source-only pointWeight expansion at 320; no field reduction --/
lemma pw_0320 : pw 320 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather160]
  rw [hwe 160 (by omega), hwe 161 (by omega), hwo 160 (by omega)]
  change 7*w (2*160) + 5*(w (2*161)) - 5*w (2*160+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0320, w_guarded_leaf_0321, w_guarded_leaf_0322]
#print axioms pw_0320

/-- finite source-only pointWeight expansion at 321; no field reduction --/
lemma pw_0321 : pw 321 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather160, gather160]
  rw [hwe 160 (by omega), hwe 162 (by omega), hwo 160 (by omega), hwo 161 (by omega)]
  change -5*(w (2*160) - ((1073741824:M)*w (2*160) + (1073741824:M)*w (2*162))) + 7*w (2*160+1) + 5*(w (2*161+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0320, w_guarded_leaf_0321, w_guarded_leaf_0323, w_guarded_leaf_0324]
#print axioms pw_0321

/-- finite source-only pointWeight expansion at 323; no field reduction --/
lemma pw_0323 : pw 323 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) := by
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
  rw [gatherGather161, gather161]
  rw [hwe 161 (by omega), hwe 163 (by omega), hwo 160 (by omega), hwo 161 (by omega), hwo 162 (by omega)]
  change -5*(w (2*161) - ((1073741824:M)*w (2*161) + (1073741824:M)*w (2*163))) + 7*w (2*161+1) + 5*(((1073741824:M)^1)*w (2*160+1) + ((1073741824:M)^1)*w (2*162+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M)))
  rw [w_guarded_leaf_0321, w_guarded_leaf_0322, w_guarded_leaf_0323, w_guarded_leaf_0325, w_guarded_leaf_0326]
#print axioms pw_0323

/-- finite source-only pointWeight expansion at 324; no field reduction --/
lemma pw_0324 : pw 324 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather162]
  rw [hwe 162 (by omega), hwe 163 (by omega), hwo 162 (by omega)]
  change 7*w (2*162) + 5*(w (2*163)) - 5*w (2*162+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0324, w_guarded_leaf_0325, w_guarded_leaf_0326]
#print axioms pw_0324

/-- finite source-only pointWeight expansion at 325; no field reduction --/
lemma pw_0325 : pw 325 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather162, gather162]
  rw [hwe 160 (by omega), hwe 162 (by omega), hwe 164 (by omega), hwo 162 (by omega), hwo 163 (by omega)]
  change -5*(w (2*162) - ((1073741824:M)*w (2*162) + (1073741824:M)^2*w (2*160) + (1073741824:M)^2*w (2*164))) + 7*w (2*162+1) + 5*(w (2*163+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0320, w_guarded_leaf_0324, w_guarded_leaf_0325, w_guarded_leaf_0327, w_guarded_leaf_0328]
#print axioms pw_0325

/-- finite source-only pointWeight expansion at 327; no field reduction --/
lemma pw_0327 : pw 327 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) := by
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
  rw [gatherGather163, gather163]
  rw [hwe 161 (by omega), hwe 163 (by omega), hwe 165 (by omega), hwo 160 (by omega), hwo 162 (by omega), hwo 163 (by omega), hwo 164 (by omega)]
  change -5*(w (2*163) - ((1073741824:M)*w (2*163) + (1073741824:M)^2*w (2*161) + (1073741824:M)^2*w (2*165))) + 7*w (2*163+1) + 5*(((1073741824:M)^1)*w (2*162+1) + ((1073741824:M)^2)*w (2*160+1) + ((1073741824:M)^2)*w (2*164+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M)))
  rw [w_guarded_leaf_0321, w_guarded_leaf_0322, w_guarded_leaf_0325, w_guarded_leaf_0326, w_guarded_leaf_0327, w_guarded_leaf_0329, w_guarded_leaf_0330]
#print axioms pw_0327

/-- finite source-only pointWeight expansion at 328; no field reduction --/
lemma pw_0328 : pw 328 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather164]
  rw [hwe 164 (by omega), hwe 165 (by omega), hwo 164 (by omega)]
  change 7*w (2*164) + 5*(w (2*165)) - 5*w (2*164+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0328, w_guarded_leaf_0329, w_guarded_leaf_0330]
#print axioms pw_0328

/-- finite source-only pointWeight expansion at 329; no field reduction --/
lemma pw_0329 : pw 329 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather164, gather164]
  rw [hwe 164 (by omega), hwe 166 (by omega), hwo 164 (by omega), hwo 165 (by omega)]
  change -5*(w (2*164) - ((1073741824:M)*w (2*164) + (1073741824:M)*w (2*166))) + 7*w (2*164+1) + 5*(w (2*165+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0328, w_guarded_leaf_0329, w_guarded_leaf_0331, w_guarded_leaf_0332]
#print axioms pw_0329

/-- finite source-only pointWeight expansion at 331; no field reduction --/
lemma pw_0331 : pw 331 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) := by
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
  rw [gatherGather165, gather165]
  rw [hwe 165 (by omega), hwe 167 (by omega), hwo 164 (by omega), hwo 165 (by omega), hwo 166 (by omega)]
  change -5*(w (2*165) - ((1073741824:M)*w (2*165) + (1073741824:M)*w (2*167))) + 7*w (2*165+1) + 5*(((1073741824:M)^1)*w (2*164+1) + ((1073741824:M)^1)*w (2*166+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M)))
  rw [w_guarded_leaf_0329, w_guarded_leaf_0330, w_guarded_leaf_0331, w_guarded_leaf_0333, w_guarded_leaf_0334]
#print axioms pw_0331

/-- finite source-only pointWeight expansion at 332; no field reduction --/
lemma pw_0332 : pw 332 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather166]
  rw [hwe 166 (by omega), hwe 167 (by omega), hwo 166 (by omega)]
  change 7*w (2*166) + 5*(w (2*167)) - 5*w (2*166+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0332, w_guarded_leaf_0333, w_guarded_leaf_0334]
#print axioms pw_0332

/-- finite source-only pointWeight expansion at 333; no field reduction --/
lemma pw_0333 : pw 333 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^3*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather166, gather166]
  rw [hwe 160 (by omega), hwe 164 (by omega), hwe 166 (by omega), hwe 168 (by omega), hwo 166 (by omega), hwo 167 (by omega)]
  change -5*(w (2*166) - ((1073741824:M)*w (2*166) + (1073741824:M)^2*w (2*164) + (1073741824:M)^3*w (2*160) + (1073741824:M)^3*w (2*168))) + 7*w (2*166+1) + 5*(w (2*167+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^3*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0320, w_guarded_leaf_0328, w_guarded_leaf_0332, w_guarded_leaf_0333, w_guarded_leaf_0335, w_guarded_leaf_0336]
#print axioms pw_0333

/-- finite source-only pointWeight expansion at 335; no field reduction --/
lemma pw_0335 : pw 335 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^3*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^3)*((0 : M))) := by
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
  rw [gatherGather167, gather167]
  rw [hwe 161 (by omega), hwe 165 (by omega), hwe 167 (by omega), hwe 169 (by omega), hwo 160 (by omega), hwo 164 (by omega), hwo 166 (by omega), hwo 167 (by omega), hwo 168 (by omega)]
  change -5*(w (2*167) - ((1073741824:M)*w (2*167) + (1073741824:M)^2*w (2*165) + (1073741824:M)^3*w (2*161) + (1073741824:M)^3*w (2*169))) + 7*w (2*167+1) + 5*(((1073741824:M)^1)*w (2*166+1) + ((1073741824:M)^2)*w (2*164+1) + ((1073741824:M)^3)*w (2*160+1) + ((1073741824:M)^3)*w (2*168+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^3*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^3)*((0 : M)))
  rw [w_guarded_leaf_0321, w_guarded_leaf_0322, w_guarded_leaf_0329, w_guarded_leaf_0330, w_guarded_leaf_0333, w_guarded_leaf_0334, w_guarded_leaf_0335, w_guarded_leaf_0337, w_guarded_leaf_0338]
#print axioms pw_0335

/-- finite source-only pointWeight expansion at 336; no field reduction --/
lemma pw_0336 : pw 336 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather168]
  rw [hwe 168 (by omega), hwe 169 (by omega), hwo 168 (by omega)]
  change 7*w (2*168) + 5*(w (2*169)) - 5*w (2*168+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0336, w_guarded_leaf_0337, w_guarded_leaf_0338]
#print axioms pw_0336

/-- finite source-only pointWeight expansion at 337; no field reduction --/
lemma pw_0337 : pw 337 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather168, gather168]
  rw [hwe 168 (by omega), hwe 170 (by omega), hwo 168 (by omega), hwo 169 (by omega)]
  change -5*(w (2*168) - ((1073741824:M)*w (2*168) + (1073741824:M)*w (2*170))) + 7*w (2*168+1) + 5*(w (2*169+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0336, w_guarded_leaf_0337, w_guarded_leaf_0339, w_guarded_leaf_0340]
#print axioms pw_0337

/-- finite source-only pointWeight expansion at 339; no field reduction --/
lemma pw_0339 : pw 339 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) := by
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
  rw [gatherGather169, gather169]
  rw [hwe 169 (by omega), hwe 171 (by omega), hwo 168 (by omega), hwo 169 (by omega), hwo 170 (by omega)]
  change -5*(w (2*169) - ((1073741824:M)*w (2*169) + (1073741824:M)*w (2*171))) + 7*w (2*169+1) + 5*(((1073741824:M)^1)*w (2*168+1) + ((1073741824:M)^1)*w (2*170+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M)))
  rw [w_guarded_leaf_0337, w_guarded_leaf_0338, w_guarded_leaf_0339, w_guarded_leaf_0341, w_guarded_leaf_0342]
#print axioms pw_0339

/-- finite source-only pointWeight expansion at 340; no field reduction --/
lemma pw_0340 : pw 340 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather170]
  rw [hwe 170 (by omega), hwe 171 (by omega), hwo 170 (by omega)]
  change 7*w (2*170) + 5*(w (2*171)) - 5*w (2*170+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0340, w_guarded_leaf_0341, w_guarded_leaf_0342]
#print axioms pw_0340

/-- finite source-only pointWeight expansion at 341; no field reduction --/
lemma pw_0341 : pw 341 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather170, gather170]
  rw [hwe 168 (by omega), hwe 170 (by omega), hwe 172 (by omega), hwo 170 (by omega), hwo 171 (by omega)]
  change -5*(w (2*170) - ((1073741824:M)*w (2*170) + (1073741824:M)^2*w (2*168) + (1073741824:M)^2*w (2*172))) + 7*w (2*170+1) + 5*(w (2*171+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0336, w_guarded_leaf_0340, w_guarded_leaf_0341, w_guarded_leaf_0343, w_guarded_leaf_0344]
#print axioms pw_0341

/-- finite source-only pointWeight expansion at 343; no field reduction --/
lemma pw_0343 : pw 343 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) := by
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
  rw [gatherGather171, gather171]
  rw [hwe 169 (by omega), hwe 171 (by omega), hwe 173 (by omega), hwo 168 (by omega), hwo 170 (by omega), hwo 171 (by omega), hwo 172 (by omega)]
  change -5*(w (2*171) - ((1073741824:M)*w (2*171) + (1073741824:M)^2*w (2*169) + (1073741824:M)^2*w (2*173))) + 7*w (2*171+1) + 5*(((1073741824:M)^1)*w (2*170+1) + ((1073741824:M)^2)*w (2*168+1) + ((1073741824:M)^2)*w (2*172+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M)))
  rw [w_guarded_leaf_0337, w_guarded_leaf_0338, w_guarded_leaf_0341, w_guarded_leaf_0342, w_guarded_leaf_0343, w_guarded_leaf_0345, w_guarded_leaf_0346]
#print axioms pw_0343

/-- finite source-only pointWeight expansion at 344; no field reduction --/
lemma pw_0344 : pw 344 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather172]
  rw [hwe 172 (by omega), hwe 173 (by omega), hwo 172 (by omega)]
  change 7*w (2*172) + 5*(w (2*173)) - 5*w (2*172+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0344, w_guarded_leaf_0345, w_guarded_leaf_0346]
#print axioms pw_0344

/-- finite source-only pointWeight expansion at 345; no field reduction --/
lemma pw_0345 : pw 345 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather172, gather172]
  rw [hwe 172 (by omega), hwe 174 (by omega), hwo 172 (by omega), hwo 173 (by omega)]
  change -5*(w (2*172) - ((1073741824:M)*w (2*172) + (1073741824:M)*w (2*174))) + 7*w (2*172+1) + 5*(w (2*173+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0344, w_guarded_leaf_0345, w_guarded_leaf_0347, w_guarded_leaf_0348]
#print axioms pw_0345

/-- finite source-only pointWeight expansion at 347; no field reduction --/
lemma pw_0347 : pw 347 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) := by
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
  rw [gatherGather173, gather173]
  rw [hwe 173 (by omega), hwe 175 (by omega), hwo 172 (by omega), hwo 173 (by omega), hwo 174 (by omega)]
  change -5*(w (2*173) - ((1073741824:M)*w (2*173) + (1073741824:M)*w (2*175))) + 7*w (2*173+1) + 5*(((1073741824:M)^1)*w (2*172+1) + ((1073741824:M)^1)*w (2*174+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M)))
  rw [w_guarded_leaf_0345, w_guarded_leaf_0346, w_guarded_leaf_0347, w_guarded_leaf_0349, w_guarded_leaf_0350]
#print axioms pw_0347

/-- finite source-only pointWeight expansion at 348; no field reduction --/
lemma pw_0348 : pw 348 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather174]
  rw [hwe 174 (by omega), hwe 175 (by omega), hwo 174 (by omega)]
  change 7*w (2*174) + 5*(w (2*175)) - 5*w (2*174+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0348, w_guarded_leaf_0349, w_guarded_leaf_0350]
#print axioms pw_0348

/-- finite source-only pointWeight expansion at 349; no field reduction --/
lemma pw_0349 : pw 349 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^4*((2147483551:M) + 576))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather174, gather174]
  rw [hwe 160 (by omega), hwe 168 (by omega), hwe 172 (by omega), hwe 174 (by omega), hwe 176 (by omega), hwo 174 (by omega), hwo 175 (by omega)]
  change -5*(w (2*174) - ((1073741824:M)*w (2*174) + (1073741824:M)^2*w (2*172) + (1073741824:M)^3*w (2*168) + (1073741824:M)^4*w (2*160) + (1073741824:M)^4*w (2*176))) + 7*w (2*174+1) + 5*(w (2*175+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^4*((2147483551:M) + 576))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0320, w_guarded_leaf_0336, w_guarded_leaf_0344, w_guarded_leaf_0348, w_guarded_leaf_0349, w_guarded_leaf_0351, transport_leaf_0352]
#print axioms pw_0349

/-- finite source-only pointWeight expansion at 351; no field reduction --/
lemma pw_0351 : pw 351 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^4*((192:M) + 576))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^4)*((0 : M)) + ((1073741824:M)^4)*((48:M))) := by
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
  rw [gatherGather175, gather175]
  rw [hwe 161 (by omega), hwe 169 (by omega), hwe 173 (by omega), hwe 175 (by omega), hwe 177 (by omega), hwo 160 (by omega), hwo 168 (by omega), hwo 172 (by omega), hwo 174 (by omega), hwo 175 (by omega), hwo 176 (by omega)]
  change -5*(w (2*175) - ((1073741824:M)*w (2*175) + (1073741824:M)^2*w (2*173) + (1073741824:M)^3*w (2*169) + (1073741824:M)^4*w (2*161) + (1073741824:M)^4*w (2*177))) + 7*w (2*175+1) + 5*(((1073741824:M)^1)*w (2*174+1) + ((1073741824:M)^2)*w (2*172+1) + ((1073741824:M)^3)*w (2*168+1) + ((1073741824:M)^4)*w (2*160+1) + ((1073741824:M)^4)*w (2*176+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^4*((576 : M)) + (1073741824:M)^4*((192:M) + 576))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^4)*((0 : M)) + ((1073741824:M)^4)*((48:M)))
  rw [w_guarded_leaf_0321, w_guarded_leaf_0322, w_guarded_leaf_0337, w_guarded_leaf_0338, w_guarded_leaf_0345, w_guarded_leaf_0346, w_guarded_leaf_0349, w_guarded_leaf_0350, w_guarded_leaf_0351, transport_leaf_0353, transport_leaf_0354]
#print axioms pw_0351

/-- finite source-only pointWeight expansion at 352; no field reduction --/
lemma pw_0352 : pw 352 = 7*((2147483551:M) + 576) + 5*((192:M) + 576) - 5*((48:M)) := by
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
  rw [gather176]
  rw [hwe 176 (by omega), hwe 177 (by omega), hwo 176 (by omega)]
  change 7*w (2*176) + 5*(w (2*177)) - 5*w (2*176+1) = 7*((2147483551:M) + 576) + 5*((192:M) + 576) - 5*((48:M))
  rw [transport_leaf_0352, transport_leaf_0353, transport_leaf_0354]
#print axioms pw_0352

/-- finite source-only pointWeight expansion at 353; no field reduction --/
lemma pw_0353 : pw 353 = -5*(((2147483551:M) + 576) - ((1073741824:M)*((2147483551:M) + 576) + (1073741824:M)*((128:M) + 576))) + 7*((48:M)) + 5*((2147483551:M)) := by
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
  rw [gatherGather176, gather176]
  rw [hwe 176 (by omega), hwe 178 (by omega), hwo 176 (by omega), hwo 177 (by omega)]
  change -5*(w (2*176) - ((1073741824:M)*w (2*176) + (1073741824:M)*w (2*178))) + 7*w (2*176+1) + 5*(w (2*177+1)) = -5*(((2147483551:M) + 576) - ((1073741824:M)*((2147483551:M) + 576) + (1073741824:M)*((128:M) + 576))) + 7*((48:M)) + 5*((2147483551:M))
  rw [transport_leaf_0352, transport_leaf_0353, transport_leaf_0355, transport_leaf_0356]
#print axioms pw_0353

/-- finite source-only pointWeight expansion at 355; no field reduction --/
lemma pw_0355 : pw 355 = -5*(((192:M) + 576) - ((1073741824:M)*((192:M) + 576) + (1073741824:M)*((2147483391:M) + 576))) + 7*((2147483551:M)) + 5*(((1073741824:M)^1)*((48:M)) + ((1073741824:M)^1)*((2147483583:M))) := by
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
  rw [gatherGather177, gather177]
  rw [hwe 177 (by omega), hwe 179 (by omega), hwo 176 (by omega), hwo 177 (by omega), hwo 178 (by omega)]
  change -5*(w (2*177) - ((1073741824:M)*w (2*177) + (1073741824:M)*w (2*179))) + 7*w (2*177+1) + 5*(((1073741824:M)^1)*w (2*176+1) + ((1073741824:M)^1)*w (2*178+1)) = -5*(((192:M) + 576) - ((1073741824:M)*((192:M) + 576) + (1073741824:M)*((2147483391:M) + 576))) + 7*((2147483551:M)) + 5*(((1073741824:M)^1)*((48:M)) + ((1073741824:M)^1)*((2147483583:M)))
  rw [transport_leaf_0353, transport_leaf_0354, transport_leaf_0355, transport_leaf_0357, transport_leaf_0358]
#print axioms pw_0355

/-- finite source-only pointWeight expansion at 356; no field reduction --/
lemma pw_0356 : pw 356 = 7*((128:M) + 576) + 5*((2147483391:M) + 576) - 5*((2147483583:M)) := by
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
  rw [gather178]
  rw [hwe 178 (by omega), hwe 179 (by omega), hwo 178 (by omega)]
  change 7*w (2*178) + 5*(w (2*179)) - 5*w (2*178+1) = 7*((128:M) + 576) + 5*((2147483391:M) + 576) - 5*((2147483583:M))
  rw [transport_leaf_0356, transport_leaf_0357, transport_leaf_0358]
#print axioms pw_0356

/-- finite source-only pointWeight expansion at 357; no field reduction --/
lemma pw_0357 : pw 357 = -5*(((128:M) + 576) - ((1073741824:M)*((128:M) + 576) + (1073741824:M)^2*((2147483551:M) + 576) + (1073741824:M)^2*((144:M) + 576))) + 7*((2147483583:M)) + 5*((128:M)) := by
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
  rw [gatherGather178, gather178]
  rw [hwe 176 (by omega), hwe 178 (by omega), hwe 180 (by omega), hwo 178 (by omega), hwo 179 (by omega)]
  change -5*(w (2*178) - ((1073741824:M)*w (2*178) + (1073741824:M)^2*w (2*176) + (1073741824:M)^2*w (2*180))) + 7*w (2*178+1) + 5*(w (2*179+1)) = -5*(((128:M) + 576) - ((1073741824:M)*((128:M) + 576) + (1073741824:M)^2*((2147483551:M) + 576) + (1073741824:M)^2*((144:M) + 576))) + 7*((2147483583:M)) + 5*((128:M))
  rw [transport_leaf_0352, transport_leaf_0356, transport_leaf_0357, transport_leaf_0359, transport_leaf_0360]
#print axioms pw_0357

/-- finite source-only pointWeight expansion at 359; no field reduction --/
lemma pw_0359 : pw 359 = -5*(((2147483391:M) + 576) - ((1073741824:M)*((2147483391:M) + 576) + (1073741824:M)^2*((192:M) + 576) + (1073741824:M)^2*((2147483359:M) + 576))) + 7*((128:M)) + 5*(((1073741824:M)^1)*((2147483583:M)) + ((1073741824:M)^2)*((48:M)) + ((1073741824:M)^2)*((2147483575:M))) := by
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
  rw [gatherGather179, gather179]
  rw [hwe 177 (by omega), hwe 179 (by omega), hwe 181 (by omega), hwo 176 (by omega), hwo 178 (by omega), hwo 179 (by omega), hwo 180 (by omega)]
  change -5*(w (2*179) - ((1073741824:M)*w (2*179) + (1073741824:M)^2*w (2*177) + (1073741824:M)^2*w (2*181))) + 7*w (2*179+1) + 5*(((1073741824:M)^1)*w (2*178+1) + ((1073741824:M)^2)*w (2*176+1) + ((1073741824:M)^2)*w (2*180+1)) = -5*(((2147483391:M) + 576) - ((1073741824:M)*((2147483391:M) + 576) + (1073741824:M)^2*((192:M) + 576) + (1073741824:M)^2*((2147483359:M) + 576))) + 7*((128:M)) + 5*(((1073741824:M)^1)*((2147483583:M)) + ((1073741824:M)^2)*((48:M)) + ((1073741824:M)^2)*((2147483575:M)))
  rw [transport_leaf_0353, transport_leaf_0354, transport_leaf_0357, transport_leaf_0358, transport_leaf_0359, transport_leaf_0361, transport_leaf_0362]
#print axioms pw_0359

/-- finite source-only pointWeight expansion at 360; no field reduction --/
lemma pw_0360 : pw 360 = 7*((144:M) + 576) + 5*((2147483359:M) + 576) - 5*((2147483575:M)) := by
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
  rw [gather180]
  rw [hwe 180 (by omega), hwe 181 (by omega), hwo 180 (by omega)]
  change 7*w (2*180) + 5*(w (2*181)) - 5*w (2*180+1) = 7*((144:M) + 576) + 5*((2147483359:M) + 576) - 5*((2147483575:M))
  rw [transport_leaf_0360, transport_leaf_0361, transport_leaf_0362]
#print axioms pw_0360

/-- finite source-only pointWeight expansion at 361; no field reduction --/
lemma pw_0361 : pw 361 = -5*(((144:M) + 576) - ((1073741824:M)*((144:M) + 576) + (1073741824:M)*((2147483455:M) + 576))) + 7*((2147483575:M)) + 5*((144:M) + 576) := by
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
  rw [gatherGather180, gather180]
  rw [hwe 180 (by omega), hwe 182 (by omega), hwo 180 (by omega), hwo 181 (by omega)]
  change -5*(w (2*180) - ((1073741824:M)*w (2*180) + (1073741824:M)*w (2*182))) + 7*w (2*180+1) + 5*(w (2*181+1)) = -5*(((144:M) + 576) - ((1073741824:M)*((144:M) + 576) + (1073741824:M)*((2147483455:M) + 576))) + 7*((2147483575:M)) + 5*((144:M) + 576)
  rw [transport_leaf_0360, transport_leaf_0361, transport_leaf_0363, transport_leaf_0364]
#print axioms pw_0361

end
end AspisV8R19.R760PointWeightChunk05
