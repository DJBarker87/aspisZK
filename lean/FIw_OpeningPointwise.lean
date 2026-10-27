import FIw_ArrayReadValue
import FIw_AssetModel
import FIw_AssetSource
import FIw_Baseline
import FIw_BuilderValue
import FIw_CoefficientMeaning
import FIw_CoefficientTransport
import FIw_CompositionAsset
import FIw_CompositionOperands
import FIw_CompositionOrigins
import FIw_CopyEndpoint
import FIw_CopyEvaluation
import FIw_CopyMeaning
import FIw_CopyTransport
import FIw_OpeningCanonical
import FIw_PackArithmetic
import FIw_PackNonvacuity
import FIw_PackSource
import FIw_PackTotal
import FIw_PackValue
import FIw_PackWide
import FIw_PublicModel
import FIw_ScalarArithmetic
import FIw_ScalarIndices
import FIw_ScalarSuffix
import FIw_SelectedValue
import FIw_SelectorIndices
import FIw_SelectorRow
import FIw_WordValue
import FIw_OpeningValues
import FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_OpeningPointwise
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)

theorem value (a : Array NQ 16#usize) (model : Usize → K)
    (values : a.val.map decode=(OraclePortStdBuilder.indices 16#usize).map model)
    (j : Fin 16) :
    FIw_ArrayValue.decoded a j=model (UScalar.ofNatCore j.val (by scalar_tac)) := by
  have slot := congrArg (fun xs : List K=>xs[j.val]?) values
  have bound : a.val.length=16 := a.property
  have hj : j.val<a.val.length := by rw [bound];exact j.isLt
  have indexBound : j.val<(16#usize).val := j.isLt
  simp only [List.getElem?_map,OraclePortStdBuilder.indices,List.getElem?_ofFn,
    dif_pos indexBound,List.getElem?_eq_getElem hj,Option.map_some,Option.some.injEq] at slot
  simpa only [Usize.ofNatCore,FIw_ArrayValue.decoded,FIw_ArrayValue.cells] using slot
#print axioms value
end AspisR1.FIw_OpeningPointwise
end

-- Final charged audit: local results only; no deployed premise removal.
#print axioms AspisR1.FIw_ArrayReadValue.value
#print axioms AspisR1.FIw_ArrayReadValue.read
#print axioms AspisR1.FIw_ArrayValue.list_set
#print axioms AspisR1.FIw_ArrayValue.update
#print axioms AspisR1.FIw_AssetModel.value
#print axioms AspisR1.FIw_AssetSource.value
#print axioms AspisR1.FIw_BuilderValue.loop
#print axioms AspisR1.FIw_BuilderValue.fromFn
#print axioms AspisR1.FIw_CoefficientMeaning.value
#print axioms AspisR1.FIw_CoefficientTransport.value
#print axioms AspisR1.FIw_CompositionAsset.value
#print axioms AspisR1.FIw_CompositionOperands.reached
#print axioms AspisR1.FIw_CompositionOrigins.reached
#print axioms AspisR1.FIw_CopyEndpoint.value
#print axioms AspisR1.FIw_CopyEvaluation.value
#print axioms AspisR1.FIw_CopyMeaning.value_exact
#print axioms AspisR1.FIw_CopyTransport.value_exact
#print axioms AspisR1.FIw_OpeningCanonical.z
#print axioms AspisR1.FIw_OpeningCanonical.succ
#print axioms AspisR1.FIw_OpeningCanonical.xor12
#print axioms AspisR1.FIw_OpeningValues.z
#print axioms AspisR1.FIw_OpeningValues.succ
#print axioms AspisR1.FIw_OpeningValues.xor12
#print axioms AspisR1.FIw_PackArithmetic.index
#print axioms AspisR1.FIw_PackArithmetic.cm_new
#print axioms AspisR1.FIw_PackArithmetic.mapped
#print axioms AspisR1.FIw_PackNonvacuity.value
#print axioms AspisR1.FIw_PackSource.generated_eq
#print axioms AspisR1.FIw_PackSource.value
#print axioms AspisR1.FIw_PackTotal.arithmetic
#print axioms AspisR1.FIw_PackTotal.source
#print axioms AspisR1.FIw_PackValue.value
#print axioms AspisR1.FIw_PackWide.value
#print axioms AspisR1.FIw_ScalarArithmetic.scalar_nat
#print axioms AspisR1.FIw_ScalarArithmetic.cm_mapped
#print axioms AspisR1.FIw_ScalarArithmetic.qm_mapped
#print axioms AspisR1.FIw_ScalarArithmetic.mul
#print axioms AspisR1.FIw_ScalarArithmetic.lift_run
#print axioms AspisR1.FIw_ScalarArithmetic.lift_value
#print axioms AspisR1.FIw_ScalarIndices.mul2
#print axioms AspisR1.FIw_ScalarIndices.mul31
#print axioms AspisR1.FIw_ScalarIndices.mul28
#print axioms AspisR1.FIw_ScalarIndices.mul63
#print axioms AspisR1.FIw_ScalarIndices.add44
#print axioms AspisR1.FIw_ScalarIndices.add508
#print axioms AspisR1.FIw_ScalarIndices.add460
#print axioms AspisR1.FIw_ScalarIndices.add1010
#print axioms AspisR1.FIw_ScalarIndices.add26
#print axioms AspisR1.FIw_ScalarIndices.add28
#print axioms AspisR1.FIw_ScalarSuffix.reached
#print axioms AspisR1.FIw_ScalarSuffix.value_exact
#print axioms AspisR1.FIw_SelectedValue.width
#print axioms AspisR1.FIw_SelectedValue.value
#print axioms AspisR1.FIw_SelectorIndices.high
#print axioms AspisR1.FIw_SelectorIndices.low
#print axioms AspisR1.FIw_SelectorRow.value_exact
#print axioms AspisR1.FIw_WordValue.mul
#print axioms AspisR1.FIw_WordValue.add
#print axioms AspisR1.Rc10_Top.deployed
#print axioms AspisR1.FIr_Top.deployed
#print axioms AspisR1.Rc10_Nonvacuity.composed
#print axioms AspisR1.FIr_Nonvacuity.composed
#print axioms FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
#print AspisR1.FIw_CompositionAsset.value
#print AspisR1.FIw_CopyEndpoint.value
#print AspisR1.FIw_AssetSource.value
#print AspisR1.FIw_PackWide.value
#print AspisR1.FIw_PackNonvacuity.value
