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
  change (1088716477<2147483647 ∧ 138480954<2147483647 ∧ 594404524<2147483647 ∧ 235888091<2147483647) ∧ (825857942<2147483647 ∧ 1279003129<2147483647 ∧ 249353404<2147483647 ∧ 1197453166<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value14_1.value) := by
  change (15687369<2147483647 ∧ 1784838689<2147483647 ∧ 398768033<2147483647 ∧ 116960670<2147483647) ∧ (610797708<2147483647 ∧ 914523711<2147483647 ∧ 721153737<2147483647 ∧ 1051484045<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value14_2.value) := by
  change (125463782<2147483647 ∧ 459900494<2147483647 ∧ 133977935<2147483647 ∧ 1569107572<2147483647) ∧ (2118312143<2147483647 ∧ 1217704526<2147483647 ∧ 1944953935<2147483647 ∧ 1697297753<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value14_3.value) := by
  change (869947202<2147483647 ∧ 14284178<2147483647 ∧ 2010150175<2147483647 ∧ 137407851<2147483647) ∧ (1719137229<2147483647 ∧ 1617323363<2147483647 ∧ 218012038<2147483647 ∧ 1815723572<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 3#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value14_3.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values14
end
