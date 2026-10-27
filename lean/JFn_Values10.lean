import JFn_Value10_0
import JFn_Value10_1
import JFn_Value10_2
import JFn_Value10_3
import JFn_ArrayBuilder
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
  change (1495862191<2147483647 ∧ 567078347<2147483647 ∧ 822330498<2147483647 ∧ 1320403121<2147483647) ∧ (1444941663<2147483647 ∧ 1346309889<2147483647 ∧ 1049237274<2147483647 ∧ 875315436<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value10_1.value) := by
  change (113909661<2147483647 ∧ 89704391<2147483647 ∧ 795026575<2147483647 ∧ 2113142288<2147483647) ∧ (1284560133<2147483647 ∧ 623893483<2147483647 ∧ 795489078<2147483647 ∧ 1526441663<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value10_2.value) := by
  change (71556150<2147483647 ∧ 2132269355<2147483647 ∧ 1374888388<2147483647 ∧ 1054874463<2147483647) ∧ (191642238<2147483647 ∧ 66970454<2147483647 ∧ 548253468<2147483647 ∧ 610343033<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value10_3.value) := by
  change (2028222263<2147483647 ∧ 814288248<2147483647 ∧ 354118641<2147483647 ∧ 1376248873<2147483647) ∧ (1642244954<2147483647 ∧ 2101120408<2147483647 ∧ 22065465<2147483647 ∧ 1602413776<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 3#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value10_3.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values10
end
