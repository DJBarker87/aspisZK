import NMX_R3_LaneObserve
import NMX_R3_LaneModels
import NMX_R3_Indices
set_option autoImplicit false
namespace NMX_R3_LaneFinish
open Aeneas Aeneas.Std Result RSL NMX_R3_ByteCarrier NMX_R3_LaneCarrier NMX_R3_LaneObserve

theorem value (b : Slice U8) (master : Array U8 32#usize) (laneId : U8)
 (next : U64) (root : Array U32 8#usize) (frontier : Array (Array U32 8#usize) 20#usize)
 (extent : b.val.length = 768) :
 observe (NMX_R3_LaneCuts.finish b master laneId next root frontier) =
 ok (NMX_R3_LaneModels.emit (b.val.map byte) (key master) (byte laneId) (long next)
  (root.val.map word) (frontier.val.map (fun row => row.val.map word))) := by
 classical
 have bumpRead : Slice.index_usize b 72#usize = ok (NCV_ZeroStep.byte b 72) := by
  simpa only [NMX_R3_Indices.v72] using
   NCV_ZeroStep.read b 72#usize (by rw [NMX_R3_Indices.v72,extent]; decide)
 have emptyRead : Array.index_usize NCV_Reference.EMPTY 20#usize =
  ok (NCV_ArrayFrame.coord NCV_Reference.EMPTY 20) := by
  simpa only [NMX_R3_Indices.v20] using NCV_ArrayRead.read NCV_Reference.EMPTY 20#usize (by scalar_tac)
 have equalRead : NCV_Reference.eq_digest root (NCV_ArrayFrame.coord NCV_Reference.EMPTY 20) =
  ok (root.val.map word == EMPTY_ROOTS.getD 20 []) := by
  rw [NMX_R3_DigestEquality.value]
  erw [NMX_R3_FrontierCarrier.empty_coordinate 20 (by decide)]
 have bumpMap : (b.val.map byte).getD 72 0 = byte (NCV_ZeroStep.byte b 72) :=
  NMX_R3_ByteIndex.mapped b.val 72
 by_cases zero : next = 0#u64
 · have nextFlag : (long next == 0) = true := by rw [zero]; rfl
   cases eqCase : (root.val.map word == EMPTY_ROOTS.getD 20 []) <;>
    simp only [NMX_R3_LaneCuts.finish, if_pos zero, emptyRead, equalRead, bumpRead,
     bind_tc_ok, through_if, returned, NMX_R3_LaneCarrier.result,
     NMX_R3_LaneCarrier.lane, NMX_R3_LaneModels.emit, TREE_DEPTH, nextFlag,
     bne, eqCase, Bool.not_true, Bool.not_false, Bool.true_and,
     Bool.false_eq_true, ↓reduceIte, bumpMap]
 · have hostNonzero : long next ≠ 0 := by
    intro same
    apply zero
    apply NMX_R3_LongBits.injective
    exact same
   have nextFlag : (long next == 0) = false := Bool.eq_false_iff.mpr (fun h => hostNonzero (beq_iff_eq.mp h))
   simp only [NMX_R3_LaneCuts.finish, if_neg zero, bumpRead, bind_tc_ok, returned,
    NMX_R3_LaneCarrier.result, NMX_R3_LaneCarrier.lane, NMX_R3_LaneModels.emit,
    nextFlag, Bool.false_and, Bool.false_eq_true, ↓reduceIte, bumpMap]
#print axioms value
end NMX_R3_LaneFinish
