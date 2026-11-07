import NMX_R3_LaneDigest
set_option autoImplicit false
namespace NMX_R3_LaneCounter
open Aeneas Aeneas.Std Result RSL NMX_R3_ByteCarrier NMX_R3_LaneCarrier NMX_R3_LaneObserve

attribute [local irreducible] RSL.le64 NCV_Reference.word64

theorem capacity (next : U64) : next > 1048576#u64 ↔ PAIR_CAPACITY < long next := by
 change 1048576 < next.val ↔ 1048576 < (long next).toNat
 rw [long_value]

theorem value (b : Slice U8) (master : Array U8 32#usize) (laneId : U8)
 (t : Slice U8) (bExtent : b.val.length = 768) (tExtent : t.val.length = 688) :
 observe (NMX_R3_LaneCuts.counter b master laneId t) =
 ok (NMX_R3_LaneModels.counter (b.val.map byte) (key master) (byte laneId) (t.val.map byte)) := by
 obtain ⟨next,call,mapped⟩ := NMX_R3_Word64.value t 8#usize
  (by rw [NMX_R3_Indices.v8,tExtent]; decide)
 have same : long next = le64 (slice (t.val.map byte) 8 16) := by
  simpa only [NMX_R3_Indices.v8] using mapped
 simp only [NMX_R3_LaneCuts.counter, call, bind_tc_ok, through_if]
 by_cases too : next > 1048576#u64
 · have bad := (capacity next).mp too
   simp only [if_pos too, returned, NMX_R3_LaneCarrier.result,
    NMX_R3_LaneModels.counter, ← same, bad, decide_true, ↓reduceIte]
 · have good : ¬ PAIR_CAPACITY < long next := fun h => too ((capacity next).mpr h)
   rw [if_neg too, NMX_R3_LaneDigest.value b master laneId t next bExtent tExtent]
   simp only [NMX_R3_LaneModels.counter, ← same, good, decide_false, Bool.false_eq_true, ↓reduceIte]
#print axioms capacity
#print axioms value
end NMX_R3_LaneCounter
