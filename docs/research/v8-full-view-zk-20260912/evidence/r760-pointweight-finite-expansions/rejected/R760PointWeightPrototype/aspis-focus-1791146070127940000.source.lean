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

namespace AspisV8R19.R760PointWeightPrototype
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

/-- finite source-only pointWeight expansion at 511; no field reduction --/
lemma pw_0511 : pw 511 = -5*(((384:M) + 576) - ((1073741824:M)*((384:M) + 576) + (1073741824:M)^2*((2147483359:M) + 576) + (1073741824:M)^3*((192:M) + 576) + (1073741824:M)^4*((2147483551:M) + 576) + (1073741824:M)^5*((576:M)) + (1073741824:M)^6*((576:M)) + (1073741824:M)^7*((576:M)) + (1073741824:M)^8*((576:M)) + (1073741824:M)^8*((576:M)))) + 7*((2147483455:M)) + 5*(((1073741824:M)^1)*((96:M)) + ((1073741824:M)^2)*((2147483575:M)) + ((1073741824:M)^3)*((48:M) + 576) + ((1073741824:M)^4)*((2147483623:M) + 576) + ((1073741824:M)^5)*((576:M)) + ((1073741824:M)^6)*((576:M)) + ((1073741824:M)^7)*((576:M)) + ((1073741824:M)^8)*((576:M)) + ((1073741824:M)^8)*((576:M))) := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  simp only [one_ne_zero, if_false]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by
    unfold zeroExtend
    rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by
    unfold zeroExtend
    rw [if_pos hi]
  rw [gatherGather255, gather255]
  rw [hwe 1 (by omega), hwe 129 (by omega), hwe 193 (by omega), hwe 225 (by omega), hwe 241 (by omega), hwe 249 (by omega), hwe 253 (by omega), hwe 255 (by omega), hwe 257 (by omega), hwo 0 (by omega), hwo 128 (by omega), hwo 192 (by omega), hwo 224 (by omega), hwo 240 (by omega), hwo 248 (by omega), hwo 252 (by omega), hwo 254 (by omega), hwo 255 (by omega), hwo 256 (by omega)]
  change -5*(w 510 - ((1073741824:M)*w 255 + (1073741824:M)^2*w 253 + (1073741824:M)^3*w 249 + (1073741824:M)^4*w 241 + (1073741824:M)^5*w 225 + (1073741824:M)^6*w 193 + (1073741824:M)^7*w 129 + (1073741824:M)^8*w 1 + (1073741824:M)^8*w 257)) + 7*w 511 + 5*(((1073741824:M)^1)*w 509 + ((1073741824:M)^2)*w 505 + ((1073741824:M)^3)*w 497 + ((1073741824:M)^4)*w 481 + ((1073741824:M)^5)*w 449 + ((1073741824:M)^6)*w 385 + ((1073741824:M)^7)*w 257 + ((1073741824:M)^8)*w 1 + ((1073741824:M)^8)*w 513) = -5*(((384:M) + 576) - ((1073741824:M)*((384:M) + 576) + (1073741824:M)^2*((2147483359:M) + 576) + (1073741824:M)^3*((192:M) + 576) + (1073741824:M)^4*((2147483551:M) + 576) + (1073741824:M)^5*((576:M)) + (1073741824:M)^6*((576:M)) + (1073741824:M)^7*((576:M)) + (1073741824:M)^8*((576:M)) + (1073741824:M)^8*((576:M)))) + 7*((2147483455:M)) + 5*(((1073741824:M)^1)*((96:M)) + ((1073741824:M)^2)*((2147483575:M)) + ((1073741824:M)^3)*((48:M) + 576) + ((1073741824:M)^4)*((2147483623:M) + 576) + ((1073741824:M)^5)*((576:M)) + ((1073741824:M)^6)*((576:M)) + ((1073741824:M)^7)*((576:M)) + ((1073741824:M)^8)*((576:M)) + ((1073741824:M)^8)*((576:M)))
  rw [w_1, w_2, w_guarded_leaf_0257, w_guarded_leaf_0258, w_guarded_leaf_0385, w_guarded_leaf_0386, w_guarded_leaf_0449, w_guarded_leaf_0450, transport_leaf_0481, transport_leaf_0482, transport_leaf_0497, transport_leaf_0498, transport_leaf_0505, transport_leaf_0506, transport_leaf_0509, transport_leaf_0510, transport_leaf_0511, w_guarded_leaf_0513, w_guarded_leaf_0514]
  rfl
#print axioms pw_0511

end
end AspisV8R19.R760PointWeightPrototype
