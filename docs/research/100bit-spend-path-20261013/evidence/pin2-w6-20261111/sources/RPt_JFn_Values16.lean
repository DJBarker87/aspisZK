import RPt_JFn_Value16_0
import RPt_JFn_Value16_1
import RPt_JFn_Value16_2
import RPt_JFn_Value16_3
import RPt_JFn_ArrayBuilder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Values16
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JFn_Value16_0.value,SAQ_RecordDecode.fromRecord JFn_Value16_1.value,SAQ_RecordDecode.fromRecord JFn_Value16_2.value,SAQ_RecordDecode.fromRecord JFn_Value16_3.value]

/-- The actual ordered op0 body, with each op21 call made on opening[672:800]. -/
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨16,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨16,by decide⟩ _ _ _ _
    JFn_Value16_0.source JFn_Value16_1.source JFn_Value16_2.source JFn_Value16_3.source

theorem canonical0 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value16_0.value) := by
  change (1943140805<2147483647 ∧ 2074602070<2147483647 ∧ 490061367<2147483647 ∧ 1955166270<2147483647) ∧ (1380003894<2147483647 ∧ 208160383<2147483647 ∧ 509210439<2147483647 ∧ 1684399206<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value16_1.value) := by
  change (1725644480<2147483647 ∧ 2113540087<2147483647 ∧ 2002525195<2147483647 ∧ 764101520<2147483647) ∧ (1311306969<2147483647 ∧ 311136457<2147483647 ∧ 1211057208<2147483647 ∧ 1838068172<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value16_2.value) := by
  change (1490989034<2147483647 ∧ 86315523<2147483647 ∧ 493200794<2147483647 ∧ 1400667862<2147483647) ∧ (492118936<2147483647 ∧ 1637575959<2147483647 ∧ 1112607338<2147483647 ∧ 1782409982<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value16_3.value) := by
  change (1630949521<2147483647 ∧ 911223934<2147483647 ∧ 1772867025<2147483647 ∧ 630485276<2147483647) ∧ (677621649<2147483647 ∧ 934193462<2147483647 ∧ 1411046907<2147483647 ∧ 172072325<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 3#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value16_3.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values16
end
