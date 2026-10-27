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
  change (1645515821<2147483647 ∧ 1240656743<2147483647 ∧ 654046506<2147483647 ∧ 879080589<2147483647) ∧ (1716804485<2147483647 ∧ 761274092<2147483647 ∧ 522936145<2147483647 ∧ 1747388490<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value16_1.value) := by
  change (761665955<2147483647 ∧ 1216452524<2147483647 ∧ 1641480485<2147483647 ∧ 657124396<2147483647) ∧ (1654126825<2147483647 ∧ 1271579678<2147483647 ∧ 1636670801<2147483647 ∧ 1414412887<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value16_2.value) := by
  change (433885726<2147483647 ∧ 799164942<2147483647 ∧ 1270989458<2147483647 ∧ 211268664<2147483647) ∧ (438802342<2147483647 ∧ 1380386303<2147483647 ∧ 900251607<2147483647 ∧ 290924911<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value16_3.value) := by
  change (824109249<2147483647 ∧ 1055461204<2147483647 ∧ 498236731<2147483647 ∧ 726239408<2147483647) ∧ (864580662<2147483647 ∧ 722374172<2147483647 ∧ 1169491654<2147483647 ∧ 676743912<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 2#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value16_2.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values16
end
