import RPt_JFn_Value10_0
import RPt_JFn_Value10_1
import RPt_JFn_Value10_2
import RPt_JFn_Value10_3
import RPt_JFn_ArrayBuilder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Values10
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JFn_Value10_0.value,SAQ_RecordDecode.fromRecord JFn_Value10_1.value,SAQ_RecordDecode.fromRecord JFn_Value10_2.value,SAQ_RecordDecode.fromRecord JFn_Value10_3.value]

/-- The actual ordered op0 body, with each op21 call made on opening[672:800]. -/
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨10,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨10,by decide⟩ _ _ _ _
    JFn_Value10_0.source JFn_Value10_1.source JFn_Value10_2.source JFn_Value10_3.source

theorem canonical0 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value10_0.value) := by
  change (374049989<2147483647 ∧ 810899026<2147483647 ∧ 1239013600<2147483647 ∧ 292396735<2147483647) ∧ (811032280<2147483647 ∧ 275866042<2147483647 ∧ 1070548688<2147483647 ∧ 130938683<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value10_1.value) := by
  change (824459537<2147483647 ∧ 1086980198<2147483647 ∧ 370444779<2147483647 ∧ 1699176490<2147483647) ∧ (677798807<2147483647 ∧ 1549522625<2147483647 ∧ 1525349176<2147483647 ∧ 1428316928<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value10_2.value) := by
  change (1710005376<2147483647 ∧ 69904474<2147483647 ∧ 304233347<2147483647 ∧ 1992865269<2147483647) ∧ (482022203<2147483647 ∧ 1433423517<2147483647 ∧ 771425924<2147483647 ∧ 1125066818<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value10_3.value) := by
  change (1777198620<2147483647 ∧ 1945946598<2147483647 ∧ 514685170<2147483647 ∧ 1553378258<2147483647) ∧ (235644209<2147483647 ∧ 160135771<2147483647 ∧ 400610329<2147483647 ∧ 172615070<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 2#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value10_2.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values10
end
