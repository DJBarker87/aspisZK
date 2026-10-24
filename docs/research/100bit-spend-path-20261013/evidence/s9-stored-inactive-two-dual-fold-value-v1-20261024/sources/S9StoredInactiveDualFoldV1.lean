import S9ActualLowModelWeightV1
import S9FinalPartsInactiveRowV1
import S9TwoDualSourceBaseV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1S9StoredInactiveDualFoldV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeS3WeightBodyV1 (W Can decode)
open AspisR1S9ActualProcessKindTensorReachedV1 (Parts)
open AspisR1S9NativeS3OuterBodyV1 (Coefficients)
open AspisR1S9InactiveFinalZeroCellV1 (cell0 exact_span_bytes_bound)
open AspisR1S9FinalPartsInactiveRowV1 (InactiveRowStored)
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- The actual stored0 source result is the two-dual-fold pairing of the
existing inactive raw row, on its SAME strict coefficient input stream.
Its alpha observations and coefficient producer are retained as source events. -/
theorem stored_inactive_row_is_dual_fold (shared : Bool) (self : weights.Weights)
    (alpha : Slice W) (f : Slice U8) (parts : Parts)
    (hspan : Slice.len f=Usize.wrapping_mul 64#usize 32#usize)
    (halpha : ∀ i x,Slice.index_usize alpha i=.ok x → Can x)
    (hstored : InactiveRowStored shared self alpha f parts hspan) :
    ∃ (a0 a1 : W) (coefficients : Coefficients)
      (hcoeff : weights.s2_grouped_inactive_pair_loop0 {start:=0#usize,«end»:=64#usize} f
        (Array.repeat 12#usize aspis_core.field.wide_exact.WideExact.ZERO)=.ok coefficients),
      Slice.index_usize alpha 0#usize=.ok a0 ∧ Slice.index_usize alpha 1#usize=.ok a1 ∧
      decode (cell0 parts)=AspisR1.RoundPairing.dot
        (fun j : Fin 64=>AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients
          (exact_span_bytes_bound f hspan) hcoeff j.val)
        (AspisR1.RoundPairing.dualFold (decode a1)
          (AspisR1.RoundPairing.dualFold (decode a0)
            AspisR1S9TwoDualSourceBaseV1.inactiveRow)) := by
  obtain ⟨a0,a1,ap0,ap1,low,before,middle,libra,coefficients,hcoeff,
    ha0,hp0,ha1,hp1,hlow,hhelper,hwrite,hactive,hread,hcan,hvalue⟩ := hstored
  have hlowModel := AspisR1S9ActualLowModelWeightV1.actual_low_success_model
    shared a0 a1 ap0 ap1
    (Array.repeat 16#usize aspis_core.field.wide_exact.WideExact.ZERO) low
    (halpha 0#usize a0 ha0) (halpha 1#usize a1 ha1) hp0 hp1 hlow
  have hlowFunction : (fun s : Fin 16=>(low.val.map decode).getD s.val 0)=
      AspisR1S9TwoDualSourceBaseV1.lowWeight (decode a0) (decode a1) := by
    funext s
    exact hlowModel s
  rw [hlowFunction] at hvalue
  have hmath := AspisR1S9TwoDualSourceBaseV1.inactive_two_dual_dot
    (decode a0) (decode a1)
    (fun j : Fin 64=>AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients
      (exact_span_bytes_bound f hspan) hcoeff j.val)
  exact ⟨a0,a1,coefficients,hcoeff,ha0,ha1,hvalue.trans hmath.symm⟩

#print axioms stored_inactive_row_is_dual_fold
end AspisR1S9StoredInactiveDualFoldV1
end
