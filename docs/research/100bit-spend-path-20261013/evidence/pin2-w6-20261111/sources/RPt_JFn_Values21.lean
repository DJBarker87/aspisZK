import RPt_JFn_Value21_0
import RPt_JFn_Value21_1
import RPt_JFn_Value21_2
import RPt_JFn_Value21_3
import RPt_JFn_ArrayBuilder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Values21
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JFn_Value21_0.value,SAQ_RecordDecode.fromRecord JFn_Value21_1.value,SAQ_RecordDecode.fromRecord JFn_Value21_2.value,SAQ_RecordDecode.fromRecord JFn_Value21_3.value]

/-- The actual ordered op0 body, with each op21 call made on opening[672:800]. -/
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨21,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨21,by decide⟩ _ _ _ _
    JFn_Value21_0.source JFn_Value21_1.source JFn_Value21_2.source JFn_Value21_3.source

theorem canonical0 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value21_0.value) := by
  change (1998674171<2147483647 ∧ 395626217<2147483647 ∧ 958276941<2147483647 ∧ 924693030<2147483647) ∧ (789732097<2147483647 ∧ 1138945636<2147483647 ∧ 1261482757<2147483647 ∧ 1745469344<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value21_1.value) := by
  change (1977283219<2147483647 ∧ 301346517<2147483647 ∧ 1294074351<2147483647 ∧ 1686920353<2147483647) ∧ (1936175910<2147483647 ∧ 412677078<2147483647 ∧ 1238035163<2147483647 ∧ 1077902535<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value21_2.value) := by
  change (155540300<2147483647 ∧ 774717320<2147483647 ∧ 1748903650<2147483647 ∧ 1052158879<2147483647) ∧ (1033653559<2147483647 ∧ 1377877085<2147483647 ∧ 50441165<2147483647 ∧ 276438515<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value21_3.value) := by
  change (485079210<2147483647 ∧ 2019598127<2147483647 ∧ 116947243<2147483647 ∧ 536337782<2147483647) ∧ (154427072<2147483647 ∧ 998021289<2147483647 ∧ 1568263779<2147483647 ∧ 1163248902<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 2#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value21_2.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values21
end
