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

namespace AspisV8R19.R760PointWeightChunk03
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

/-- finite source-only pointWeight expansion at 232; no field reduction --/
lemma pw_0232 : pw 232 = 7*((108:M)) + 5*((2147483431:M)) - 5*((2147483593:M) + 576) := by
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
  rw [gather116]
  rw [hwe 116 (by omega), hwe 117 (by omega), hwo 116 (by omega)]
  change 7*w (2*116) + 5*(w (2*117)) - 5*w (2*116+1) = 7*((108:M)) + 5*((2147483431:M)) - 5*((2147483593:M) + 576)
  rw [transport_leaf_0232, transport_leaf_0233, transport_leaf_0234]
#print axioms pw_0232

/-- finite source-only pointWeight expansion at 233; no field reduction --/
lemma pw_0233 : pw 233 = -5*(((108:M)) - ((1073741824:M)*((108:M)) + (1073741824:M)*((2147483503:M)))) + 7*((2147483593:M) + 576) + 5*((108:M) + 576) := by
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
  rw [gatherGather116, gather116]
  rw [hwe 116 (by omega), hwe 118 (by omega), hwo 116 (by omega), hwo 117 (by omega)]
  change -5*(w (2*116) - ((1073741824:M)*w (2*116) + (1073741824:M)*w (2*118))) + 7*w (2*116+1) + 5*(w (2*117+1)) = -5*(((108:M)) - ((1073741824:M)*((108:M)) + (1073741824:M)*((2147483503:M)))) + 7*((2147483593:M) + 576) + 5*((108:M) + 576)
  rw [transport_leaf_0232, transport_leaf_0233, transport_leaf_0235, transport_leaf_0236]
#print axioms pw_0233

/-- finite source-only pointWeight expansion at 234; no field reduction --/
lemma pw_0234 : pw 234 = 7*((2147483431:M)) + 5*(((1073741824:M)^1)*((108:M)) + ((1073741824:M)^1)*((2147483503:M))) - 5*((108:M) + 576) := by
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
  rw [gather117]
  rw [hwe 116 (by omega), hwe 117 (by omega), hwe 118 (by omega), hwo 117 (by omega)]
  change 7*w (2*117) + 5*(((1073741824:M)^1)*w (2*116) + ((1073741824:M)^1)*w (2*118)) - 5*w (2*117+1) = 7*((2147483431:M)) + 5*(((1073741824:M)^1)*((108:M)) + ((1073741824:M)^1)*((2147483503:M))) - 5*((108:M) + 576)
  rw [transport_leaf_0232, transport_leaf_0234, transport_leaf_0235, transport_leaf_0236]
#print axioms pw_0234

/-- finite source-only pointWeight expansion at 236; no field reduction --/
lemma pw_0236 : pw 236 = 7*((2147483503:M)) + 5*((288:M)) - 5*((72:M) + 576) := by
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
  rw [gather118]
  rw [hwe 118 (by omega), hwe 119 (by omega), hwo 118 (by omega)]
  change 7*w (2*118) + 5*(w (2*119)) - 5*w (2*118+1) = 7*((2147483503:M)) + 5*((288:M)) - 5*((72:M) + 576)
  rw [transport_leaf_0236, transport_leaf_0237, transport_leaf_0238]
#print axioms pw_0236

/-- finite source-only pointWeight expansion at 237; no field reduction --/
lemma pw_0237 : pw 237 = -5*(((2147483503:M)) - ((1073741824:M)*((2147483503:M)) + (1073741824:M)^2*((108:M)) + (1073741824:M)^3*((2147483575:M)) + (1073741824:M)^3*((144:M)))) + 7*((72:M) + 576) + 5*((2147483503:M) + 576) := by
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
  rw [gatherGather118, gather118]
  rw [hwe 112 (by omega), hwe 116 (by omega), hwe 118 (by omega), hwe 120 (by omega), hwo 118 (by omega), hwo 119 (by omega)]
  change -5*(w (2*118) - ((1073741824:M)*w (2*118) + (1073741824:M)^2*w (2*116) + (1073741824:M)^3*w (2*112) + (1073741824:M)^3*w (2*120))) + 7*w (2*118+1) + 5*(w (2*119+1)) = -5*(((2147483503:M)) - ((1073741824:M)*((2147483503:M)) + (1073741824:M)^2*((108:M)) + (1073741824:M)^3*((2147483575:M)) + (1073741824:M)^3*((144:M)))) + 7*((72:M) + 576) + 5*((2147483503:M) + 576)
  rw [transport_leaf_0224, transport_leaf_0232, transport_leaf_0236, transport_leaf_0237, transport_leaf_0239, transport_leaf_0240]
#print axioms pw_0237

/-- finite source-only pointWeight expansion at 238; no field reduction --/
lemma pw_0238 : pw 238 = 7*((288:M)) + 5*(((1073741824:M)^1)*((2147483503:M)) + ((1073741824:M)^2)*((108:M)) + ((1073741824:M)^3)*((2147483575:M)) + ((1073741824:M)^3)*((144:M))) - 5*((2147483503:M) + 576) := by
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
  rw [gather119]
  rw [hwe 112 (by omega), hwe 116 (by omega), hwe 118 (by omega), hwe 119 (by omega), hwe 120 (by omega), hwo 119 (by omega)]
  change 7*w (2*119) + 5*(((1073741824:M)^1)*w (2*118) + ((1073741824:M)^2)*w (2*116) + ((1073741824:M)^3)*w (2*112) + ((1073741824:M)^3)*w (2*120)) - 5*w (2*119+1) = 7*((288:M)) + 5*(((1073741824:M)^1)*((2147483503:M)) + ((1073741824:M)^2)*((108:M)) + ((1073741824:M)^3)*((2147483575:M)) + ((1073741824:M)^3)*((144:M))) - 5*((2147483503:M) + 576)
  rw [transport_leaf_0224, transport_leaf_0232, transport_leaf_0236, transport_leaf_0238, transport_leaf_0239, transport_leaf_0240]
#print axioms pw_0238

/-- finite source-only pointWeight expansion at 240; no field reduction --/
lemma pw_0240 : pw 240 = 7*((144:M)) + 5*((2147483359:M) + 576) - 5*((2147483575:M) + 576) := by
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
  rw [gather120]
  rw [hwe 120 (by omega), hwe 121 (by omega), hwo 120 (by omega)]
  change 7*w (2*120) + 5*(w (2*121)) - 5*w (2*120+1) = 7*((144:M)) + 5*((2147483359:M) + 576) - 5*((2147483575:M) + 576)
  rw [transport_leaf_0240, transport_leaf_0241, transport_leaf_0242]
#print axioms pw_0240

/-- finite source-only pointWeight expansion at 241; no field reduction --/
lemma pw_0241 : pw 241 = -5*(((144:M)) - ((1073741824:M)*((144:M)) + (1073741824:M)*((2147483455:M) + 576))) + 7*((2147483575:M) + 576) + 5*((144:M)) := by
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
  rw [gatherGather120, gather120]
  rw [hwe 120 (by omega), hwe 122 (by omega), hwo 120 (by omega), hwo 121 (by omega)]
  change -5*(w (2*120) - ((1073741824:M)*w (2*120) + (1073741824:M)*w (2*122))) + 7*w (2*120+1) + 5*(w (2*121+1)) = -5*(((144:M)) - ((1073741824:M)*((144:M)) + (1073741824:M)*((2147483455:M) + 576))) + 7*((2147483575:M) + 576) + 5*((144:M))
  rw [transport_leaf_0240, transport_leaf_0241, transport_leaf_0243, transport_leaf_0244]
#print axioms pw_0241

/-- finite source-only pointWeight expansion at 243; no field reduction --/
lemma pw_0243 : pw 243 = -5*(((2147483359:M) + 576) - ((1073741824:M)*((2147483359:M) + 576) + (1073741824:M)*((384:M) + 576))) + 7*((144:M)) + 5*(((1073741824:M)^1)*((2147483575:M) + 576) + ((1073741824:M)^1)*((96:M))) := by
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
  rw [gatherGather121, gather121]
  rw [hwe 121 (by omega), hwe 123 (by omega), hwo 120 (by omega), hwo 121 (by omega), hwo 122 (by omega)]
  change -5*(w (2*121) - ((1073741824:M)*w (2*121) + (1073741824:M)*w (2*123))) + 7*w (2*121+1) + 5*(((1073741824:M)^1)*w (2*120+1) + ((1073741824:M)^1)*w (2*122+1)) = -5*(((2147483359:M) + 576) - ((1073741824:M)*((2147483359:M) + 576) + (1073741824:M)*((384:M) + 576))) + 7*((144:M)) + 5*(((1073741824:M)^1)*((2147483575:M) + 576) + ((1073741824:M)^1)*((96:M)))
  rw [transport_leaf_0241, transport_leaf_0242, transport_leaf_0243, transport_leaf_0245, transport_leaf_0246]
#print axioms pw_0243

/-- finite source-only pointWeight expansion at 244; no field reduction --/
lemma pw_0244 : pw 244 = 7*((2147483455:M) + 576) + 5*((384:M) + 576) - 5*((96:M)) := by
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
  rw [gather122]
  rw [hwe 122 (by omega), hwe 123 (by omega), hwo 122 (by omega)]
  change 7*w (2*122) + 5*(w (2*123)) - 5*w (2*122+1) = 7*((2147483455:M) + 576) + 5*((384:M) + 576) - 5*((96:M))
  rw [transport_leaf_0244, transport_leaf_0245, transport_leaf_0246]
#print axioms pw_0244

/-- finite source-only pointWeight expansion at 245; no field reduction --/
lemma pw_0245 : pw 245 = -5*(((2147483455:M) + 576) - ((1073741824:M)*((2147483455:M) + 576) + (1073741824:M)^2*((144:M)) + (1073741824:M)^2*((2147483431:M) + 576))) + 7*((96:M)) + 5*((2147483455:M)) := by
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
  rw [gatherGather122, gather122]
  rw [hwe 120 (by omega), hwe 122 (by omega), hwe 124 (by omega), hwo 122 (by omega), hwo 123 (by omega)]
  change -5*(w (2*122) - ((1073741824:M)*w (2*122) + (1073741824:M)^2*w (2*120) + (1073741824:M)^2*w (2*124))) + 7*w (2*122+1) + 5*(w (2*123+1)) = -5*(((2147483455:M) + 576) - ((1073741824:M)*((2147483455:M) + 576) + (1073741824:M)^2*((144:M)) + (1073741824:M)^2*((2147483431:M) + 576))) + 7*((96:M)) + 5*((2147483455:M))
  rw [transport_leaf_0240, transport_leaf_0244, transport_leaf_0245, transport_leaf_0247, transport_leaf_0248]
#print axioms pw_0245

/-- finite source-only pointWeight expansion at 247; no field reduction --/
lemma pw_0247 : pw 247 = -5*(((384:M) + 576) - ((1073741824:M)*((384:M) + 576) + (1073741824:M)^2*((2147483359:M) + 576) + (1073741824:M)^2*((432:M) + 576))) + 7*((2147483455:M)) + 5*(((1073741824:M)^1)*((96:M)) + ((1073741824:M)^2)*((2147483575:M) + 576) + ((1073741824:M)^2)*((108:M))) := by
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
  rw [gatherGather123, gather123]
  rw [hwe 121 (by omega), hwe 123 (by omega), hwe 125 (by omega), hwo 120 (by omega), hwo 122 (by omega), hwo 123 (by omega), hwo 124 (by omega)]
  change -5*(w (2*123) - ((1073741824:M)*w (2*123) + (1073741824:M)^2*w (2*121) + (1073741824:M)^2*w (2*125))) + 7*w (2*123+1) + 5*(((1073741824:M)^1)*w (2*122+1) + ((1073741824:M)^2)*w (2*120+1) + ((1073741824:M)^2)*w (2*124+1)) = -5*(((384:M) + 576) - ((1073741824:M)*((384:M) + 576) + (1073741824:M)^2*((2147483359:M) + 576) + (1073741824:M)^2*((432:M) + 576))) + 7*((2147483455:M)) + 5*(((1073741824:M)^1)*((96:M)) + ((1073741824:M)^2)*((2147483575:M) + 576) + ((1073741824:M)^2)*((108:M)))
  rw [transport_leaf_0241, transport_leaf_0242, transport_leaf_0245, transport_leaf_0246, transport_leaf_0247, transport_leaf_0249, transport_leaf_0250]
#print axioms pw_0247

/-- finite source-only pointWeight expansion at 248; no field reduction --/
lemma pw_0248 : pw 248 = 7*((2147483431:M) + 576) + 5*((432:M) + 576) - 5*((108:M)) := by
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
  rw [gather124]
  rw [hwe 124 (by omega), hwe 125 (by omega), hwo 124 (by omega)]
  change 7*w (2*124) + 5*(w (2*125)) - 5*w (2*124+1) = 7*((2147483431:M) + 576) + 5*((432:M) + 576) - 5*((108:M))
  rw [transport_leaf_0248, transport_leaf_0249, transport_leaf_0250]
#print axioms pw_0248

/-- finite source-only pointWeight expansion at 249; no field reduction --/
lemma pw_0249 : pw 249 = -5*(((2147483431:M) + 576) - ((1073741824:M)*((2147483431:M) + 576) + (1073741824:M)*((288:M) + 576))) + 7*((108:M)) + 5*((2147483431:M)) := by
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
  rw [gatherGather124, gather124]
  rw [hwe 124 (by omega), hwe 126 (by omega), hwo 124 (by omega), hwo 125 (by omega)]
  change -5*(w (2*124) - ((1073741824:M)*w (2*124) + (1073741824:M)*w (2*126))) + 7*w (2*124+1) + 5*(w (2*125+1)) = -5*(((2147483431:M) + 576) - ((1073741824:M)*((2147483431:M) + 576) + (1073741824:M)*((288:M) + 576))) + 7*((108:M)) + 5*((2147483431:M))
  rw [transport_leaf_0248, transport_leaf_0249, transport_leaf_0251, transport_leaf_0252]
#print axioms pw_0249

/-- finite source-only pointWeight expansion at 251; no field reduction --/
lemma pw_0251 : pw 251 = -5*(((432:M) + 576) - ((1073741824:M)*((432:M) + 576) + (1073741824:M)*((2147483071:M) + 576))) + 7*((2147483431:M)) + 5*(((1073741824:M)^1)*((108:M)) + ((1073741824:M)^1)*((2147483503:M))) := by
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
  rw [gatherGather125, gather125]
  rw [hwe 125 (by omega), hwe 127 (by omega), hwo 124 (by omega), hwo 125 (by omega), hwo 126 (by omega)]
  change -5*(w (2*125) - ((1073741824:M)*w (2*125) + (1073741824:M)*w (2*127))) + 7*w (2*125+1) + 5*(((1073741824:M)^1)*w (2*124+1) + ((1073741824:M)^1)*w (2*126+1)) = -5*(((432:M) + 576) - ((1073741824:M)*((432:M) + 576) + (1073741824:M)*((2147483071:M) + 576))) + 7*((2147483431:M)) + 5*(((1073741824:M)^1)*((108:M)) + ((1073741824:M)^1)*((2147483503:M)))
  rw [transport_leaf_0249, transport_leaf_0250, transport_leaf_0251, transport_leaf_0253, transport_leaf_0254]
#print axioms pw_0251

/-- finite source-only pointWeight expansion at 252; no field reduction --/
lemma pw_0252 : pw 252 = 7*((288:M) + 576) + 5*((2147483071:M) + 576) - 5*((2147483503:M)) := by
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
  rw [gather126]
  rw [hwe 126 (by omega), hwe 127 (by omega), hwo 126 (by omega)]
  change 7*w (2*126) + 5*(w (2*127)) - 5*w (2*126+1) = 7*((288:M) + 576) + 5*((2147483071:M) + 576) - 5*((2147483503:M))
  rw [transport_leaf_0252, transport_leaf_0253, transport_leaf_0254]
#print axioms pw_0252

/-- finite source-only pointWeight expansion at 253; no field reduction --/
lemma pw_0253 : pw 253 = -5*(((288:M) + 576) - ((1073741824:M)*((288:M) + 576) + (1073741824:M)^2*((2147483431:M) + 576) + (1073741824:M)^3*((144:M)) + (1073741824:M)^4*((2147483575:M)) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^6*((0 : M)) + (1073741824:M)^7*((576:M)) + (1073741824:M)^7*((576 : M)))) + 7*((2147483503:M)) + 5*((288:M) + 576) := by
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
  rw [gatherGather126, gather126]
  rw [hwe 0 (by omega), hwe 64 (by omega), hwe 96 (by omega), hwe 112 (by omega), hwe 120 (by omega), hwe 124 (by omega), hwe 126 (by omega), hwe 128 (by omega), hwo 126 (by omega), hwo 127 (by omega)]
  change -5*(w (2*126) - ((1073741824:M)*w (2*126) + (1073741824:M)^2*w (2*124) + (1073741824:M)^3*w (2*120) + (1073741824:M)^4*w (2*112) + (1073741824:M)^5*w (2*96) + (1073741824:M)^6*w (2*64) + (1073741824:M)^7*w (2*0) + (1073741824:M)^7*w (2*128))) + 7*w (2*126+1) + 5*(w (2*127+1)) = -5*(((288:M) + 576) - ((1073741824:M)*((288:M) + 576) + (1073741824:M)^2*((2147483431:M) + 576) + (1073741824:M)^3*((144:M)) + (1073741824:M)^4*((2147483575:M)) + (1073741824:M)^5*((576 : M)) + (1073741824:M)^6*((0 : M)) + (1073741824:M)^7*((576:M)) + (1073741824:M)^7*((576 : M)))) + 7*((2147483503:M)) + 5*((288:M) + 576)
  rw [w_0, w_guarded_leaf_0128, w_guarded_leaf_0192, transport_leaf_0224, transport_leaf_0240, transport_leaf_0248, transport_leaf_0252, transport_leaf_0253, transport_leaf_0255, w_guarded_leaf_0256]
#print axioms pw_0253

/-- finite source-only pointWeight expansion at 256; no field reduction --/
lemma pw_0256 : pw 256 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather128]
  rw [hwe 128 (by omega), hwe 129 (by omega), hwo 128 (by omega)]
  change 7*w (2*128) + 5*(w (2*129)) - 5*w (2*128+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0256, w_guarded_leaf_0257, w_guarded_leaf_0258]
#print axioms pw_0256

/-- finite source-only pointWeight expansion at 257; no field reduction --/
lemma pw_0257 : pw 257 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather128, gather128]
  rw [hwe 128 (by omega), hwe 130 (by omega), hwo 128 (by omega), hwo 129 (by omega)]
  change -5*(w (2*128) - ((1073741824:M)*w (2*128) + (1073741824:M)*w (2*130))) + 7*w (2*128+1) + 5*(w (2*129+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0256, w_guarded_leaf_0257, w_guarded_leaf_0259, w_guarded_leaf_0260]
#print axioms pw_0257

/-- finite source-only pointWeight expansion at 259; no field reduction --/
lemma pw_0259 : pw 259 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) := by
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
  rw [gatherGather129, gather129]
  rw [hwe 129 (by omega), hwe 131 (by omega), hwo 128 (by omega), hwo 129 (by omega), hwo 130 (by omega)]
  change -5*(w (2*129) - ((1073741824:M)*w (2*129) + (1073741824:M)*w (2*131))) + 7*w (2*129+1) + 5*(((1073741824:M)^1)*w (2*128+1) + ((1073741824:M)^1)*w (2*130+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M)))
  rw [w_guarded_leaf_0257, w_guarded_leaf_0258, w_guarded_leaf_0259, w_guarded_leaf_0261, w_guarded_leaf_0262]
#print axioms pw_0259

/-- finite source-only pointWeight expansion at 260; no field reduction --/
lemma pw_0260 : pw 260 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather130]
  rw [hwe 130 (by omega), hwe 131 (by omega), hwo 130 (by omega)]
  change 7*w (2*130) + 5*(w (2*131)) - 5*w (2*130+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0260, w_guarded_leaf_0261, w_guarded_leaf_0262]
#print axioms pw_0260

/-- finite source-only pointWeight expansion at 261; no field reduction --/
lemma pw_0261 : pw 261 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather130, gather130]
  rw [hwe 128 (by omega), hwe 130 (by omega), hwe 132 (by omega), hwo 130 (by omega), hwo 131 (by omega)]
  change -5*(w (2*130) - ((1073741824:M)*w (2*130) + (1073741824:M)^2*w (2*128) + (1073741824:M)^2*w (2*132))) + 7*w (2*130+1) + 5*(w (2*131+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0256, w_guarded_leaf_0260, w_guarded_leaf_0261, w_guarded_leaf_0263, w_guarded_leaf_0264]
#print axioms pw_0261

/-- finite source-only pointWeight expansion at 263; no field reduction --/
lemma pw_0263 : pw 263 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M))) := by
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
  rw [gatherGather131, gather131]
  rw [hwe 129 (by omega), hwe 131 (by omega), hwe 133 (by omega), hwo 128 (by omega), hwo 130 (by omega), hwo 131 (by omega), hwo 132 (by omega)]
  change -5*(w (2*131) - ((1073741824:M)*w (2*131) + (1073741824:M)^2*w (2*129) + (1073741824:M)^2*w (2*133))) + 7*w (2*131+1) + 5*(((1073741824:M)^1)*w (2*130+1) + ((1073741824:M)^2)*w (2*128+1) + ((1073741824:M)^2)*w (2*132+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^2*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^2)*((0 : M)))
  rw [w_guarded_leaf_0257, w_guarded_leaf_0258, w_guarded_leaf_0261, w_guarded_leaf_0262, w_guarded_leaf_0263, w_guarded_leaf_0265, w_guarded_leaf_0266]
#print axioms pw_0263

/-- finite source-only pointWeight expansion at 264; no field reduction --/
lemma pw_0264 : pw 264 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather132]
  rw [hwe 132 (by omega), hwe 133 (by omega), hwo 132 (by omega)]
  change 7*w (2*132) + 5*(w (2*133)) - 5*w (2*132+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0264, w_guarded_leaf_0265, w_guarded_leaf_0266]
#print axioms pw_0264

/-- finite source-only pointWeight expansion at 265; no field reduction --/
lemma pw_0265 : pw 265 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather132, gather132]
  rw [hwe 132 (by omega), hwe 134 (by omega), hwo 132 (by omega), hwo 133 (by omega)]
  change -5*(w (2*132) - ((1073741824:M)*w (2*132) + (1073741824:M)*w (2*134))) + 7*w (2*132+1) + 5*(w (2*133+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0264, w_guarded_leaf_0265, w_guarded_leaf_0267, w_guarded_leaf_0268]
#print axioms pw_0265

/-- finite source-only pointWeight expansion at 267; no field reduction --/
lemma pw_0267 : pw 267 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) := by
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
  rw [gatherGather133, gather133]
  rw [hwe 133 (by omega), hwe 135 (by omega), hwo 132 (by omega), hwo 133 (by omega), hwo 134 (by omega)]
  change -5*(w (2*133) - ((1073741824:M)*w (2*133) + (1073741824:M)*w (2*135))) + 7*w (2*133+1) + 5*(((1073741824:M)^1)*w (2*132+1) + ((1073741824:M)^1)*w (2*134+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M)))
  rw [w_guarded_leaf_0265, w_guarded_leaf_0266, w_guarded_leaf_0267, w_guarded_leaf_0269, w_guarded_leaf_0270]
#print axioms pw_0267

/-- finite source-only pointWeight expansion at 268; no field reduction --/
lemma pw_0268 : pw 268 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather134]
  rw [hwe 134 (by omega), hwe 135 (by omega), hwo 134 (by omega)]
  change 7*w (2*134) + 5*(w (2*135)) - 5*w (2*134+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0268, w_guarded_leaf_0269, w_guarded_leaf_0270]
#print axioms pw_0268

/-- finite source-only pointWeight expansion at 269; no field reduction --/
lemma pw_0269 : pw 269 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^3*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather134, gather134]
  rw [hwe 128 (by omega), hwe 132 (by omega), hwe 134 (by omega), hwe 136 (by omega), hwo 134 (by omega), hwo 135 (by omega)]
  change -5*(w (2*134) - ((1073741824:M)*w (2*134) + (1073741824:M)^2*w (2*132) + (1073741824:M)^3*w (2*128) + (1073741824:M)^3*w (2*136))) + 7*w (2*134+1) + 5*(w (2*135+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^3*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0256, w_guarded_leaf_0264, w_guarded_leaf_0268, w_guarded_leaf_0269, w_guarded_leaf_0271, w_guarded_leaf_0272]
#print axioms pw_0269

/-- finite source-only pointWeight expansion at 271; no field reduction --/
lemma pw_0271 : pw 271 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^3*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^3)*((0 : M))) := by
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
  rw [gatherGather135, gather135]
  rw [hwe 129 (by omega), hwe 133 (by omega), hwe 135 (by omega), hwe 137 (by omega), hwo 128 (by omega), hwo 132 (by omega), hwo 134 (by omega), hwo 135 (by omega), hwo 136 (by omega)]
  change -5*(w (2*135) - ((1073741824:M)*w (2*135) + (1073741824:M)^2*w (2*133) + (1073741824:M)^3*w (2*129) + (1073741824:M)^3*w (2*137))) + 7*w (2*135+1) + 5*(((1073741824:M)^1)*w (2*134+1) + ((1073741824:M)^2)*w (2*132+1) + ((1073741824:M)^3)*w (2*128+1) + ((1073741824:M)^3)*w (2*136+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)^2*((576 : M)) + (1073741824:M)^3*((576 : M)) + (1073741824:M)^3*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^2)*((0 : M)) + ((1073741824:M)^3)*((0 : M)) + ((1073741824:M)^3)*((0 : M)))
  rw [w_guarded_leaf_0257, w_guarded_leaf_0258, w_guarded_leaf_0265, w_guarded_leaf_0266, w_guarded_leaf_0269, w_guarded_leaf_0270, w_guarded_leaf_0271, w_guarded_leaf_0273, w_guarded_leaf_0274]
#print axioms pw_0271

/-- finite source-only pointWeight expansion at 272; no field reduction --/
lemma pw_0272 : pw 272 = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M)) := by
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
  rw [gather136]
  rw [hwe 136 (by omega), hwe 137 (by omega), hwo 136 (by omega)]
  change 7*w (2*136) + 5*(w (2*137)) - 5*w (2*136+1) = 7*((576 : M)) + 5*((576 : M)) - 5*((0 : M))
  rw [w_guarded_leaf_0272, w_guarded_leaf_0273, w_guarded_leaf_0274]
#print axioms pw_0272

/-- finite source-only pointWeight expansion at 273; no field reduction --/
lemma pw_0273 : pw 273 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M)) := by
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
  rw [gatherGather136, gather136]
  rw [hwe 136 (by omega), hwe 138 (by omega), hwo 136 (by omega), hwo 137 (by omega)]
  change -5*(w (2*136) - ((1073741824:M)*w (2*136) + (1073741824:M)*w (2*138))) + 7*w (2*136+1) + 5*(w (2*137+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*((0 : M))
  rw [w_guarded_leaf_0272, w_guarded_leaf_0273, w_guarded_leaf_0275, w_guarded_leaf_0276]
#print axioms pw_0273

/-- finite source-only pointWeight expansion at 275; no field reduction --/
lemma pw_0275 : pw 275 = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M))) := by
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
  rw [gatherGather137, gather137]
  rw [hwe 137 (by omega), hwe 139 (by omega), hwo 136 (by omega), hwo 137 (by omega), hwo 138 (by omega)]
  change -5*(w (2*137) - ((1073741824:M)*w (2*137) + (1073741824:M)*w (2*139))) + 7*w (2*137+1) + 5*(((1073741824:M)^1)*w (2*136+1) + ((1073741824:M)^1)*w (2*138+1)) = -5*(((576 : M)) - ((1073741824:M)*((576 : M)) + (1073741824:M)*((576 : M)))) + 7*((0 : M)) + 5*(((1073741824:M)^1)*((0 : M)) + ((1073741824:M)^1)*((0 : M)))
  rw [w_guarded_leaf_0273, w_guarded_leaf_0274, w_guarded_leaf_0275, w_guarded_leaf_0277, w_guarded_leaf_0278]
#print axioms pw_0275

end
end AspisV8R19.R760PointWeightChunk03
