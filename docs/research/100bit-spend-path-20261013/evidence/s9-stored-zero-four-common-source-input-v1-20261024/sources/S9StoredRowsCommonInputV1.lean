import S9StoredInactiveDualFoldV1
import S9StoredPrivateDualFoldV1
import S9PointSameInputV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1S9StoredRowsCommonInputV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeS3WeightBodyV1 (W Can decode)
open AspisR1S9ActualProcessKindTensorReachedV1 (Parts)
open AspisR1S9InactiveFinalZeroCellV1 (cell0 exact_span_bytes_bound)
open AspisR1S9ActiveFourValueStepV1 (cell4)
open AspisR1S9ActiveOriginalCoefficientsV1 (Q)
open AspisR1S9ActualPairOldCarrierScalarV1 (toHelperQ)
open AspisR1S9SharedSumObservationsV1 (fieldValue finIndex)
abbrev E := AspisWideTower.WideExact
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

def commonInput (f : Slice U8) (h64 : 64≤64) : Fin 64 → E := fun i=>fieldValue f (finIndex h64 i)

theorem strict_stream_eq_common (f : Slice U8)
    (coefficients : AspisR1S9NativeS3CoefficientBodyV1.C)
    (hbytes : 2048≤f.val.length)
    (hcoeff : weights.s2_grouped_inactive_pair_loop0 {start:=0#usize,«end»:=64#usize} f
      (Array.repeat 12#usize aspis_core.field.wide_exact.WideExact.ZERO)=.ok coefficients)
    (h64 : 64≤64) :
    (fun j : Fin 64=>AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients hbytes hcoeff j.val)=
      commonInput f h64 := by
  funext i
  exact (AspisR1S9PointSameInputV1.point_fieldValue_same_input f coefficients hbytes hcoeff h64 i).symm

/-- The same finite source field observations are used for point and inactive
rows; no equality of independently chosen coefficient vectors is required. -/
theorem stored_inactive_common_input (shared : Bool) (self : weights.Weights)
    (alpha : Slice W) (f : Slice U8) (parts : Parts)
    (hspan : Slice.len f=Usize.wrapping_mul 64#usize 32#usize)
    (halpha : ∀ i x,Slice.index_usize alpha i=.ok x → Can x)
    (hstored : AspisR1S9FinalPartsInactiveRowV1.InactiveRowStored shared self alpha f parts hspan)
    (h64 : 64≤64) :
    ∃ a0 a1 : W,Slice.index_usize alpha 0#usize=.ok a0 ∧ Slice.index_usize alpha 1#usize=.ok a1 ∧
      decode (cell0 parts)=AspisR1.RoundPairing.dot (commonInput f h64)
        (AspisR1.RoundPairing.dualFold (decode a1)
          (AspisR1.RoundPairing.dualFold (decode a0) AspisR1S9TwoDualSourceBaseV1.inactiveRow)) := by
  obtain ⟨a0,a1,coefficients,hcoeff,ha0,ha1,hvalue⟩ :=
    AspisR1S9StoredInactiveDualFoldV1.stored_inactive_row_is_dual_fold
      shared self alpha f parts hspan halpha hstored
  have hi := strict_stream_eq_common f coefficients (exact_span_bytes_bound f hspan) hcoeff h64
  rw [hi] at hvalue
  exact ⟨a0,a1,ha0,ha1,hvalue⟩

/-- Actual private and point rows use exactly the same source field stream,
while preserving both actual extra/seed observations. -/
theorem stored_private_common_input (shared : Bool) (self : weights.Weights)
    (alpha : Slice W) (f : Slice U8) (parts : Parts)
    (hspan : Slice.len f=Usize.wrapping_mul 64#usize 32#usize)
    (halpha : ∀ i x,Slice.index_usize alpha i=.ok x → Can x)
    (hstored : AspisR1S9FinalPartsActiveRowV1.ActiveRowStored shared self alpha f parts hspan)
    (h64 : 64≤64) :
    ∃ (a0 a1 : W) (q0 q1 : Q),
      Slice.index_usize alpha 0#usize=.ok a0 ∧ Slice.index_usize alpha 1#usize=.ok a1 ∧
      Array.index_usize self.extra 0#usize=.ok q0 ∧ Array.index_usize self.extra 1#usize=.ok q1 ∧
      decode (cell4 parts)=AspisR1.RoundPairing.dot (commonInput f h64)
        (AspisR1.RoundPairing.dualFold (decode a1)
          (AspisR1.RoundPairing.dualFold (decode a0)
            (AspisR1S9TwoDualSourcePrivateV1.privateRow
              (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q0))
              (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q1))))) := by
  obtain ⟨a0,a1,coefficients,hcoeff,q0,q1,ha0,ha1,hq0,hq1,hvalue⟩ :=
    AspisR1S9StoredPrivateDualFoldV1.stored_private_row_is_dual_fold
      shared self alpha f parts hspan halpha hstored
  have hi := strict_stream_eq_common f coefficients (exact_span_bytes_bound f hspan) hcoeff h64
  rw [hi] at hvalue
  exact ⟨a0,a1,q0,q1,ha0,ha1,hq0,hq1,hvalue⟩

#print axioms strict_stream_eq_common
#print axioms stored_inactive_common_input
#print axioms stored_private_common_input
end AspisR1S9StoredRowsCommonInputV1
end
