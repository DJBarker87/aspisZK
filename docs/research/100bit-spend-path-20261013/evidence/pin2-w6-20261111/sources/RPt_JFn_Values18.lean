import RPt_JFn_Value18_0
import RPt_JFn_Value18_1
import RPt_JFn_Value18_2
import RPt_JFn_Value18_3
import RPt_JFn_ArrayBuilder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Values18
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JFn_Value18_0.value,SAQ_RecordDecode.fromRecord JFn_Value18_1.value,SAQ_RecordDecode.fromRecord JFn_Value18_2.value,SAQ_RecordDecode.fromRecord JFn_Value18_3.value]

/-- The actual ordered op0 body, with each op21 call made on opening[672:800]. -/
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨18,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨18,by decide⟩ _ _ _ _
    JFn_Value18_0.source JFn_Value18_1.source JFn_Value18_2.source JFn_Value18_3.source

theorem canonical0 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value18_0.value) := by
  change (1515211635<2147483647 ∧ 1950825126<2147483647 ∧ 1364620015<2147483647 ∧ 1236044610<2147483647) ∧ (535878359<2147483647 ∧ 820886170<2147483647 ∧ 1654338214<2147483647 ∧ 554179219<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value18_1.value) := by
  change (351723840<2147483647 ∧ 1503950670<2147483647 ∧ 388709472<2147483647 ∧ 904853844<2147483647) ∧ (735519757<2147483647 ∧ 1947411987<2147483647 ∧ 1229790838<2147483647 ∧ 1026011618<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value18_2.value) := by
  change (431612475<2147483647 ∧ 307287655<2147483647 ∧ 1580826793<2147483647 ∧ 98238640<2147483647) ∧ (1636951069<2147483647 ∧ 235738414<2147483647 ∧ 1265871093<2147483647 ∧ 1656922321<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value18_3.value) := by
  change (1946268781<2147483647 ∧ 2045203187<2147483647 ∧ 612001671<2147483647 ∧ 1435461045<2147483647) ∧ (1524664501<2147483647 ∧ 969183992<2147483647 ∧ 748807309<2147483647 ∧ 185251879<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 3#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value18_3.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values18
end
