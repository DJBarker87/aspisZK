import S9StoredRowsCommonInputV1
import S9SharedHighConstructorModelV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1S9StoredZeroFourSameAlphaV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeS3WeightBodyV1 (W Can decode)
open AspisR1S9ActualProcessKindTensorReachedV1 (Parts)
open AspisR1S9InactiveFinalZeroCellV1 (cell0)
open AspisR1S9ActiveFourValueStepV1 (cell4)
open AspisR1S9ActiveOriginalCoefficientsV1 (Q)
open AspisR1S9ActualPairOldCarrierScalarV1 (toHelperQ)
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- The exact source-observation vector selected by the existing point-row
model, including its original opaque bound evidence. -/
def input (f : Slice U8) : Fin 64 → AspisWideTower.WideExact :=
  AspisR1S9StoredRowsCommonInputV1.commonInput f
    AspisR1S9SharedHighConstructorModelV1.rowValue._proof_1

/-- OUTPUT on one supplied parts array and the one supplied alpha pair.
Actual source extra/seed read witnesses remain in the conclusion. -/
def Meanings (self : weights.Weights) (f : Slice U8) (parts : Parts) (a0 a1 : W) : Prop :=
  ∃ q0 q1 : Q,
    Array.index_usize self.extra 0#usize=.ok q0 ∧ Array.index_usize self.extra 1#usize=.ok q1 ∧
    decode (cell0 parts)=AspisR1.RoundPairing.dot (input f)
      (AspisR1.RoundPairing.dualFold (decode a1)
        (AspisR1.RoundPairing.dualFold (decode a0) AspisR1S9TwoDualSourceBaseV1.inactiveRow)) ∧
    decode (cell4 parts)=AspisR1.RoundPairing.dot (input f)
      (AspisR1.RoundPairing.dualFold (decode a1)
        (AspisR1.RoundPairing.dualFold (decode a0)
          (AspisR1S9TwoDualSourcePrivateV1.privateRow
            (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q0))
            (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q1)))))

/-- Same-read determinism identifies both derived alpha pairs with the ONE
supplied source pair. No independent input stream, seed/vector or desired
folded value is introduced. Canonicality is the already-derived reader guard. -/
theorem paired_stored_rows_same_alpha (shared : Bool) (self : weights.Weights)
    (alpha : Slice W) (f : Slice U8) (parts : Parts) (a0 a1 : W)
    (hspan : Slice.len f=Usize.wrapping_mul 64#usize 32#usize)
    (halpha : ∀ i x,Slice.index_usize alpha i=.ok x → Can x)
    (hinactive : AspisR1S9FinalPartsInactiveRowV1.InactiveRowStored shared self alpha f parts hspan)
    (hprivate : AspisR1S9FinalPartsActiveRowV1.ActiveRowStored shared self alpha f parts hspan)
    (ha0 : Slice.index_usize alpha 0#usize=.ok a0)
    (ha1 : Slice.index_usize alpha 1#usize=.ok a1) : Meanings self f parts a0 a1 := by
  obtain ⟨x0,x1,hx0,hx1,hzero⟩ :=
    AspisR1S9StoredRowsCommonInputV1.stored_inactive_common_input
      shared self alpha f parts hspan halpha hinactive
      AspisR1S9SharedHighConstructorModelV1.rowValue._proof_1
  have ex0 : x0=a0 := Result.ok.inj (hx0.symm.trans ha0)
  have ex1 : x1=a1 := Result.ok.inj (hx1.symm.trans ha1)
  subst x0
  subst x1
  obtain ⟨y0,y1,q0,q1,hy0,hy1,hq0,hq1,hfour⟩ :=
    AspisR1S9StoredRowsCommonInputV1.stored_private_common_input
      shared self alpha f parts hspan halpha hprivate
      AspisR1S9SharedHighConstructorModelV1.rowValue._proof_1
  have ey0 : y0=a0 := Result.ok.inj (hy0.symm.trans ha0)
  have ey1 : y1=a1 := Result.ok.inj (hy1.symm.trans ha1)
  subst y0
  subst y1
  exact ⟨q0,q1,hq0,hq1,hzero,hfour⟩

#print axioms paired_stored_rows_same_alpha
end AspisR1S9StoredZeroFourSameAlphaV1
end
