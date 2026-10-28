import NDO_JFz_TX2_Gates
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_QueryReads
open Aeneas Aeneas.Std Result

def selector (i : Fin 12) : Usize := Usize.ofNat ((JFv_TX2_Rows.query i).val%4)
  (by have h : (JFv_TX2_Rows.query i).val%4<4 := Nat.mod_lt _ (by decide);scalar_tac)

theorem query (i : Fin 12) :
    Array.index_usize JFo_Prepared.value.queries (JFv_TX2_GeometryReads.cursor i)=ok (JFv_TX2_Rows.query i) := by
  fin_cases i <;> rfl

theorem alpha0 : Array.index_usize JFo_Prepared.value.alpha 0#usize=ok JFq_Alpha0.scalar := rfl
theorem alpha1 : Array.index_usize JFo_Prepared.value.alpha 1#usize=ok JFq_Alpha1.scalar := rfl

theorem opening (i : Fin 12) :
    Port4B_Opening.opening JFx_NativeBytes.proof (JFv_TX2_GeometryReads.cursor i)=
      ok (JFo_Opening.value (JFn_Values.position i)) := JFo_Opening.call (JFn_Values.position i)

theorem remainder (i : Fin 12) :
    (UScalar.cast .Usize (JFv_TX2_Rows.query i))%4#usize=ok (selector i) := by
  have hv : (UScalar.cast .Usize (JFv_TX2_Rows.query i)).val=(JFv_TX2_Rows.query i).val := by
    fin_cases i <;> scalar_tac
  simpa only [selector,hv] using CheckpointBytesArithmetic.rem_four (UScalar.cast .Usize (JFv_TX2_Rows.query i))

theorem selected (i : Fin 12) :
    Array.index_usize (JFn_Values.value i) (selector i)=ok (JFz_TX2_Gates.selected i) :=
  JFz_TX2_Gates.selected_read i
#print axioms query
#print axioms alpha0
#print axioms alpha1
#print axioms opening
#print axioms remainder
#print axioms selected
end AspisR1.JGc_TX2_QueryReads
end
