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
  change (1336948798<2147483647 ∧ 1302427356<2147483647 ∧ 686826955<2147483647 ∧ 63018621<2147483647) ∧ (1969556263<2147483647 ∧ 1062281234<2147483647 ∧ 1040474459<2147483647 ∧ 830773486<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value18_1.value) := by
  change (808561352<2147483647 ∧ 692747672<2147483647 ∧ 361546220<2147483647 ∧ 1358250188<2147483647) ∧ (1110874099<2147483647 ∧ 1029653036<2147483647 ∧ 2119524575<2147483647 ∧ 1885260697<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value18_2.value) := by
  change (1116855082<2147483647 ∧ 137448918<2147483647 ∧ 1138851925<2147483647 ∧ 2070500897<2147483647) ∧ (1549137507<2147483647 ∧ 1596122514<2147483647 ∧ 137204697<2147483647 ∧ 278395007<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value18_3.value) := by
  change (2006696531<2147483647 ∧ 1889902675<2147483647 ∧ 1845847409<2147483647 ∧ 862601474<2147483647) ∧ (579825865<2147483647 ∧ 1158804485<2147483647 ∧ 792340213<2147483647 ∧ 645239520<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 0#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value18_0.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values18
end
