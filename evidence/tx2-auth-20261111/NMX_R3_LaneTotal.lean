import NMX_R3_LaneHeader
import NMX_R3_LaneModelEquality
set_option autoImplicit false
namespace NMX_R3_LaneTotal
open Aeneas Aeneas.Std Result RSL NMX_R3_ByteCarrier NMX_R3_LaneCarrier NMX_R3_LaneObserve
attribute [local irreducible] TX2_217.frontierLoop TX2_217.decodeDigestCanonical NCV_Reference.decode_lane_ref

theorem extract (read : Result Native) (model : Option LaneState) (h : observe read = ok model) :
 ∃ r, read = ok r ∧ result r = model := by
 cases read with
 | fail e => cases h
 | div => cases h
 | ok r => exact ⟨r,rfl,Result.ok.inj h⟩

/-- Every native result and every slice length. Extent is split by the first
source check here, never supplied as an own-input clause. -/
theorem value (b : Slice U8) :
 ∃ r, NCV_Reference.decode_lane_ref b = ok r ∧ result r = TX2_217.laneDecode (b.val.map byte) := by
 by_cases extent : b.val.length = 768
 · apply extract
   rw [←NMX_R3_LaneCuts.factor]
   have check : Slice.len b = 768#usize := by
    apply UScalar.eq_of_val_eq
    simpa only [Slice.len, Usize.ofNatCore, UScalar.ofNatCore_val_eq, NMX_R3_Indices.v768] using extent
   have guard : (Slice.len b != 768#usize) = false := by rw [check]; decide
   simp only [NMX_R3_LaneCuts.run, guard, Bool.false_eq_true, ↓reduceIte]
   rw [NMX_R3_LaneHeader.value b extent,
    NMX_R3_LaneModelEquality.value (b.val.map byte) (by simpa only [List.length_map] using extent)]
 · have call := NCV_Reject.lane b extent
   refine ⟨.Err (),call,?_⟩
   have bad : TX2_217.headerBad (b.val.map byte) = true := by
    simp only [TX2_217.headerBad, List.length_map,
     show (b.val.length != LANE_ACCOUNT_BYTES)=true by simp only [LANE_ACCOUNT_BYTES, bne_iff_ne]; exact extent,
     Bool.true_or]
   simp only [result, TX2_217.laneDecode, bad, ↓reduceIte]
#print axioms extract
#print axioms value
end NMX_R3_LaneTotal
