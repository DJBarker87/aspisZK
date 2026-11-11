import RPt_JFn_Value17_0
import RPt_JFn_Value17_1
import RPt_JFn_Value17_2
import RPt_JFn_Value17_3
import RPt_JFn_ArrayBuilder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Values17
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [SAQ_RecordDecode.fromRecord JFn_Value17_0.value,SAQ_RecordDecode.fromRecord JFn_Value17_1.value,SAQ_RecordDecode.fromRecord JFn_Value17_2.value,SAQ_RecordDecode.fromRecord JFn_Value17_3.value]

/-- The actual ordered op0 body, with each op21 call made on opening[672:800]. -/
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨17,by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨17,by decide⟩ _ _ _ _
    JFn_Value17_0.source JFn_Value17_1.source JFn_Value17_2.source JFn_Value17_3.source

theorem canonical0 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value17_0.value) := by
  change (886984016<2147483647 ∧ 1673620336<2147483647 ∧ 629925544<2147483647 ∧ 95752793<2147483647) ∧ (1869066086<2147483647 ∧ 42714032<2147483647 ∧ 1842474849<2147483647 ∧ 1140923496<2147483647)
  omega
#print axioms canonical0

theorem canonical1 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value17_1.value) := by
  change (1467468668<2147483647 ∧ 828769198<2147483647 ∧ 406842905<2147483647 ∧ 1335051684<2147483647) ∧ (1423164564<2147483647 ∧ 2143467764<2147483647 ∧ 707724359<2147483647 ∧ 1378533288<2147483647)
  omega
#print axioms canonical1

theorem canonical2 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value17_2.value) := by
  change (1664209590<2147483647 ∧ 313979865<2147483647 ∧ 585096830<2147483647 ∧ 643674109<2147483647) ∧ (610390208<2147483647 ∧ 1367192630<2147483647 ∧ 489982316<2147483647 ∧ 1026289982<2147483647)
  omega
#print axioms canonical2

theorem canonical3 : Port4C_QueryArithmetic.CanonE (SAQ_RecordDecode.fromRecord JFn_Value17_3.value) := by
  change (1533361844<2147483647 ∧ 1685616080<2147483647 ∧ 1469829951<2147483647 ∧ 752219743<2147483647) ∧ (583190322<2147483647 ∧ 562192870<2147483647 ∧ 1850249811<2147483647 ∧ 1500539814<2147483647)
  omega
#print axioms canonical3

theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
  · exact canonical0
  · exact canonical1
  · exact canonical2
  · exact canonical3

theorem selected : Array.index_usize value 1#usize=ok (SAQ_RecordDecode.fromRecord JFn_Value17_1.value) := rfl
#print axioms selected

#print axioms source
#print axioms canonical
end AspisR1.JFn_Values17
end
