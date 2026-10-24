import S9PrivateFieldDotTransportV1
import S9FinalPartsActiveRowV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1S9StoredPrivateDualFoldV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeS3WeightBodyV1 (W Can decode)
open AspisR1S9ActualProcessKindTensorReachedV1 (Parts)
open AspisR1S9NativeS3CoefficientBodyV1 (C)
open AspisR1S9ActiveOriginalCoefficientsV1 (Q)
open AspisR1S9ActiveFourValueStepV1 (cell4)
open AspisR1S9ActualPairOldCarrierScalarV1 (toHelperQ)
open AspisR1S9InactiveFinalZeroCellV1 (exact_span_bytes_bound)
open AspisR1S9FinalPartsActiveRowV1 (ActiveRowStored)
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- Actual final parts4 pairs its SAME strict input stream with two dual
folds of the first56 seed-power private row. Actual alpha/extra reads remain
source events; there is no independent seed/vector/source-success premise. -/
theorem stored_private_row_is_dual_fold (shared : Bool) (self : weights.Weights)
    (alpha : Slice W) (f : Slice U8) (parts : Parts)
    (hspan : Slice.len f=Usize.wrapping_mul 64#usize 32#usize)
    (halpha : ∀ i x,Slice.index_usize alpha i=.ok x → Can x)
    (hstored : ActiveRowStored shared self alpha f parts hspan) :
    ∃ (a0 a1 : W) (coefficients : C)
      (hcoeff : weights.s2_grouped_inactive_pair_loop0 {start:=0#usize,«end»:=64#usize} f
        (Array.repeat 12#usize aspis_core.field.wide_exact.WideExact.ZERO)=.ok coefficients)
      (q0 q1 : Q),
      Slice.index_usize alpha 0#usize=.ok a0 ∧ Slice.index_usize alpha 1#usize=.ok a1 ∧
      Array.index_usize self.extra 0#usize=.ok q0 ∧ Array.index_usize self.extra 1#usize=.ok q1 ∧
      decode (cell4 parts)=AspisR1.RoundPairing.dot
        (fun j : Fin 64=>AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients
          (exact_span_bytes_bound f hspan) hcoeff j.val)
        (AspisR1.RoundPairing.dualFold (decode a1)
          (AspisR1.RoundPairing.dualFold (decode a0)
            (AspisR1S9TwoDualSourcePrivateV1.privateRow
              (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q0))
              (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q1))))) := by
  obtain ⟨a0,a1,ap0,ap1,low,inactive,before,middle,libra,coefficients,hcoeff,q0,q1,
    ha0,hp0,ha1,hp1,hlow,hhelper,hwrite,hlibra,hactive,hzero,hq0,hq1,hread,hcan,hvalue⟩ := hstored
  have hA0 := AspisR1S9PrivateScaledBaseModelV1.actual_scaled_base_model
    ActiveRowStored._proof_3 a0 ap0 (halpha 0#usize a0 ha0) hp0
  have hA1 := AspisR1S9PrivateScaledBaseModelV1.actual_scaled_base_model
    ActiveRowStored._proof_3 a1 ap1 (halpha 1#usize a1 ha1) hp1
  conv at hvalue => rhs;rw [hA0,hA1]
  have hform := AspisR1S9PrivateFieldDotTransportV1.native_dot_operator_eq
    (fun j : Fin 4=>AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients
      (exact_span_bytes_bound f hspan) hcoeff j.val)
    (fun j=>AspisR1.S2LibraFactoredIdentity.original
      (AspisR1.S2LibraFactoredIdentity.scaled
        (AspisR1S9TwoDualSourceBaseV1.powers (decode a0)) AspisR1.RoundPairing.quarter)
      (AspisR1.S2LibraFactoredIdentity.scaled
        (AspisR1S9TwoDualSourceBaseV1.powers (decode a1)) AspisR1.RoundPairing.quarter)
      (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q0))
      (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q1)) j)
  have hmath := AspisR1S9PrivateFieldDotTransportV1.generic_private_dot_api
    (decode a0) (decode a1)
    (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q0))
    (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q1))
    (fun j : Fin 64=>AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients
      (exact_span_bytes_bound f hspan) hcoeff j.val)
  run_tac Lean.Elab.Tactic.withMainContext do
    let names := #[`AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.M,
      `AspisR1S9BodyPrefixPolynomialSumsV1.E,`AspisR1S9PrivateFieldDotTransportV1.E,
      `AspisR1S9PrivateScaledBaseModelV1.E,`AspisR1S9NativeWideDecodedArithmeticV1.E]
    for user in #[`hvalue,`hform,`hmath] do
      let hd ← Lean.Meta.getLocalDeclFromUserName user
      let ht ← Lean.instantiateMVars hd.type
      let ht ← Lean.Meta.deltaExpand ht names.contains
      let g ← Lean.Elab.Tactic.getMainGoal
      Lean.Elab.Tactic.replaceMainGoal [←g.replaceLocalDeclDefEq hd.fvarId ht]
  have hfinal := hvalue.trans (hform.trans hmath)
  refine ⟨a0,a1,coefficients,hcoeff,q0,q1,ha0,ha1,hq0,hq1,?_⟩
  run_tac Lean.Elab.Tactic.withMainContext do
    let names := #[`AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.M,
      `AspisR1S9BodyPrefixPolynomialSumsV1.E,`AspisR1S9PrivateFieldDotTransportV1.E,
      `AspisR1S9PrivateScaledBaseModelV1.E,`AspisR1S9NativeWideDecodedArithmeticV1.E]
    let gt ← Lean.Elab.Tactic.getMainTarget
    let gt ← Lean.instantiateMVars gt
    let gt ← Lean.Meta.deltaExpand gt names.contains
    let g ← Lean.Elab.Tactic.getMainGoal
    Lean.Elab.Tactic.replaceMainGoal [←g.replaceTargetDefEq gt]
  exact hfinal

#print axioms stored_private_row_is_dual_fold
end AspisR1S9StoredPrivateDualFoldV1
end
