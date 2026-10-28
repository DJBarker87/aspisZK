import NDO_JFw_TX2_Query0
import NDO_JFz_TX2_Q1_Query
import NDO_JFz_TX2_Q0_Line
import NDO_JFz_TX2_Q1_Line
import NDO_JFz_TX2_Q2_Gate
import NDO_JFz_TX2_Q3_Gate
import NDO_JFz_TX2_Q4_Gate
import NDO_JFz_TX2_Q5_Gate
import NDO_JFz_TX2_Q6_Gate
import NDO_JFz_TX2_Q7_Gate
import NDO_JFz_TX2_Q8_Gate
import NDO_JFz_TX2_Q9_Gate
import NDO_JFz_TX2_Q10_Gate
import NDO_JFz_TX2_Q11_Gate
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Gates
open Aeneas Aeneas.Std Result
def selected (i : Fin 12) : SAQ_WideABI.E := match i.val with
  | 0 => JFv_TX2_Query0Obligation.selected
  | 1 => JFz_TX2_Q1_Query.selected
  | 2 => JFz_TX2_Q2_Query.selected
  | 3 => JFz_TX2_Q3_Query.selected
  | 4 => JFz_TX2_Q4_Query.selected
  | 5 => JFz_TX2_Q5_Query.selected
  | 6 => JFz_TX2_Q6_Query.selected
  | 7 => JFz_TX2_Q7_Query.selected
  | 8 => JFz_TX2_Q8_Query.selected
  | 9 => JFz_TX2_Q9_Query.selected
  | 10 => JFz_TX2_Q10_Query.selected
  | _ => JFz_TX2_Q11_Query.selected
def lineValue (i : Fin 12) : SAQ_WideABI.E := match i.val with
  | 0 => JFz_TX2_Q0_Line.value
  | 1 => JFz_TX2_Q1_Line.value
  | 2 => JFz_TX2_Q2_Line.value
  | 3 => JFz_TX2_Q3_Line.value
  | 4 => JFz_TX2_Q4_Line.value
  | 5 => JFz_TX2_Q5_Line.value
  | 6 => JFz_TX2_Q6_Line.value
  | 7 => JFz_TX2_Q7_Line.value
  | 8 => JFz_TX2_Q8_Line.value
  | 9 => JFz_TX2_Q9_Line.value
  | 10 => JFz_TX2_Q10_Line.value
  | _ => JFz_TX2_Q11_Line.value
theorem circle {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) (i : Fin 12) :
    FIp_CircleQuery.circle JFq_Alpha0.scalar (JFs_TX2_Dots.value i)
      (JFv_TX2_CircleGeometry.inverse err seed i)=ok (selected i) := by
  fin_cases i
  · exact JFw_TX2_Query0.source err seed
  · exact JFz_TX2_Q1_Query.source err seed
  · exact JFz_TX2_Q2_Query.source err seed
  · exact JFz_TX2_Q3_Query.source err seed
  · exact JFz_TX2_Q4_Query.source err seed
  · exact JFz_TX2_Q5_Query.source err seed
  · exact JFz_TX2_Q6_Query.source err seed
  · exact JFz_TX2_Q7_Query.source err seed
  · exact JFz_TX2_Q8_Query.source err seed
  · exact JFz_TX2_Q9_Query.source err seed
  · exact JFz_TX2_Q10_Query.source err seed
  · exact JFz_TX2_Q11_Query.source err seed
theorem line {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) (i : Fin 12) :
    SAQ_LineQuery.line JFq_Alpha1.scalar (JFn_Values.value i)
      (JFv_TX2_CircleGeometry.inverse err seed i)=ok (lineValue i) := by
  fin_cases i
  · exact JFz_TX2_Q0_Line.source err seed
  · exact JFz_TX2_Q1_Line.source err seed
  · exact JFz_TX2_Q2_Line.source err seed
  · exact JFz_TX2_Q3_Line.source err seed
  · exact JFz_TX2_Q4_Line.source err seed
  · exact JFz_TX2_Q5_Line.source err seed
  · exact JFz_TX2_Q6_Line.source err seed
  · exact JFz_TX2_Q7_Line.source err seed
  · exact JFz_TX2_Q8_Line.source err seed
  · exact JFz_TX2_Q9_Line.source err seed
  · exact JFz_TX2_Q10_Line.source err seed
  · exact JFz_TX2_Q11_Line.source err seed
theorem canonical {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) (i : Fin 12) :
    Port4C_QueryArithmetic.CanonE (lineValue i) :=
  (SAQ_LineQuery.exact_line _ _ _ _ (line err seed i)).2

theorem selected_read (i : Fin 12) :
    Array.index_usize (JFn_Values.value i)
      (Usize.ofNat ((JFv_TX2_Rows.query i).val%4) (by have h : (JFv_TX2_Rows.query i).val%4<4 := Nat.mod_lt _ (by decide);scalar_tac))=ok (selected i) := by
  fin_cases i
  · exact JFv_TX2_Query0Obligation.selected_read
  · exact JFz_TX2_Q1_Query.selected_read
  · exact JFz_TX2_Q2_Query.selected_read
  · exact JFz_TX2_Q3_Query.selected_read
  · exact JFz_TX2_Q4_Query.selected_read
  · exact JFz_TX2_Q5_Query.selected_read
  · exact JFz_TX2_Q6_Query.selected_read
  · exact JFz_TX2_Q7_Query.selected_read
  · exact JFz_TX2_Q8_Query.selected_read
  · exact JFz_TX2_Q9_Query.selected_read
  · exact JFz_TX2_Q10_Query.selected_read
  · exact JFz_TX2_Q11_Query.selected_read
#print axioms circle
#print axioms line
#print axioms canonical
#print axioms selected_read
end AspisR1.JFz_TX2_Gates
end
