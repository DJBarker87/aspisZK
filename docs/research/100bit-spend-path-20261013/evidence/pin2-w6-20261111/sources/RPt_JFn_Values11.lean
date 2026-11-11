import RPt_JFn_Value11_0
import RPt_JFn_Value11_1
import RPt_JFn_Value11_2
import RPt_JFn_Value11_3
import RPt_JFn_ArrayBuilder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Values11
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JFn_Value11_0.value,SAQ_RecordDecode.fromRecord JFn_Value11_1.value,SAQ_RecordDecode.fromRecord JFn_Value11_2.value,SAQ_RecordDecode.fromRecord JFn_Value11_3.value]

/-- The actual ordered op0 body, with each op21 call made on opening[672:800]. -/
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨11,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨11,by decide⟩ _ _ _ _
    JFn_Value11_0.source JFn_Value11_1.source JFn_Value11_2.source JFn_Value11_3.source

theorem canonical0 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value11_0.value) := by
  change (1598026270<2147483647 ∧ 1237898973<2147483647 ∧ 1093807600<2147483647 ∧ 1713880413<2147483647) ∧ (1875346198<2147483647 ∧ 1659232959<2147483647 ∧ 1943169504<2147483647 ∧ 676349701<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value11_1.value) := by
  change (1746203600<2147483647 ∧ 2067791870<2147483647 ∧ 1447939218<2147483647 ∧ 399708723<2147483647) ∧ (973402300<2147483647 ∧ 905140847<2147483647 ∧ 188966629<2147483647 ∧ 25385630<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value11_2.value) := by
  change (1535126234<2147483647 ∧ 2135816786<2147483647 ∧ 1275823322<2147483647 ∧ 2133881279<2147483647) ∧ (610325850<2147483647 ∧ 1482803285<2147483647 ∧ 1811084822<2147483647 ∧ 416659997<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value11_3.value) := by
  change (81368700<2147483647 ∧ 1473351868<2147483647 ∧ 1226801916<2147483647 ∧ 319860901<2147483647) ∧ (983478372<2147483647 ∧ 1607393014<2147483647 ∧ 899039073<2147483647 ∧ 128869319<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 1#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value11_1.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values11
end
