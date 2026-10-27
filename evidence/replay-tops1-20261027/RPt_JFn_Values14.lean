import RPt_JFn_Value14_0
import RPt_JFn_Value14_1
import RPt_JFn_Value14_2
import RPt_JFn_Value14_3
import RPt_JFn_ArrayBuilder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Values14
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JFn_Value14_0.value,SAQ_RecordDecode.fromRecord JFn_Value14_1.value,SAQ_RecordDecode.fromRecord JFn_Value14_2.value,SAQ_RecordDecode.fromRecord JFn_Value14_3.value]

/-- The actual ordered op0 body, with each op21 call made on opening[672:800]. -/
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨14,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨14,by decide⟩ _ _ _ _
    JFn_Value14_0.source JFn_Value14_1.source JFn_Value14_2.source JFn_Value14_3.source

theorem canonical0 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value14_0.value) := by
  change (273788683<2147483647 ∧ 1773826581<2147483647 ∧ 260407785<2147483647 ∧ 791315104<2147483647) ∧ (1317719530<2147483647 ∧ 1055406027<2147483647 ∧ 801805620<2147483647 ∧ 1906357217<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value14_1.value) := by
  change (1424593160<2147483647 ∧ 1293249796<2147483647 ∧ 348390295<2147483647 ∧ 1333414861<2147483647) ∧ (749271607<2147483647 ∧ 1040919152<2147483647 ∧ 1068818580<2147483647 ∧ 2102458512<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value14_2.value) := by
  change (1725591817<2147483647 ∧ 1600368105<2147483647 ∧ 1962128425<2147483647 ∧ 1423876966<2147483647) ∧ (1892905843<2147483647 ∧ 254724859<2147483647 ∧ 1294731904<2147483647 ∧ 88775738<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value14_3.value) := by
  change (135209354<2147483647 ∧ 168254927<2147483647 ∧ 1172642875<2147483647 ∧ 449892866<2147483647) ∧ (1545500196<2147483647 ∧ 1578417873<2147483647 ∧ 1609871249<2147483647 ∧ 1739085228<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 1#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value14_1.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values14
end
