import JFn_Value19_0
import JFn_Value19_1
import JFn_Value19_2
import JFn_Value19_3
import JFn_ArrayBuilder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Values19
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JFn_Value19_0.value,SAQ_RecordDecode.fromRecord JFn_Value19_1.value,SAQ_RecordDecode.fromRecord JFn_Value19_2.value,SAQ_RecordDecode.fromRecord JFn_Value19_3.value]

/-- The actual ordered op0 body, with each op21 call made on opening[672:800]. -/
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨19,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨19,by decide⟩ _ _ _ _
    JFn_Value19_0.source JFn_Value19_1.source JFn_Value19_2.source JFn_Value19_3.source

theorem canonical0 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value19_0.value) := by
  change (295666010<2147483647 ∧ 486718680<2147483647 ∧ 1088486258<2147483647 ∧ 1300289649<2147483647) ∧ (631420592<2147483647 ∧ 40313731<2147483647 ∧ 1271260829<2147483647 ∧ 330825150<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value19_1.value) := by
  change (1739407730<2147483647 ∧ 1033905986<2147483647 ∧ 397093821<2147483647 ∧ 1718230613<2147483647) ∧ (2017808454<2147483647 ∧ 1510689143<2147483647 ∧ 1776877386<2147483647 ∧ 557169103<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value19_2.value) := by
  change (1755286952<2147483647 ∧ 56799981<2147483647 ∧ 970306746<2147483647 ∧ 1862977856<2147483647) ∧ (635210495<2147483647 ∧ 728242439<2147483647 ∧ 637094972<2147483647 ∧ 841182003<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value19_3.value) := by
  change (1460124800<2147483647 ∧ 178026518<2147483647 ∧ 1230459742<2147483647 ∧ 1596807589<2147483647) ∧ (736291746<2147483647 ∧ 2010145050<2147483647 ∧ 1010173706<2147483647 ∧ 1855023846<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 1#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value19_1.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values19
end
