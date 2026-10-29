import PV_B3P_ClaimSuccess227
import PV_B3P_P227_13a
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem mask_columns10 :
    aspis_core.state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS=10#usize := by
  unfold aspis_core.state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
  rfl

theorem c1_columns16 : reference_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1=16#usize := by
  unfold reference_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
  rfl

theorem mask_loop_total (claims : Array aspis_core.field.QM31 84#usize)
    (output : Array aspis_core.field.QM31 10#usize) (column : Usize)
    (hc : column.val≤10) :
    Success (reference_terminal.composition_parts_loop0 claims output column) := by
  unfold reference_terminal.composition_parts_loop0
  refine loop_total _ (fun x : Array aspis_core.field.QM31 10#usize × Usize => 10-x.2.val)
    (fun x => x.2.val≤10) ?_ (output,column) hc
  rintro ⟨w,i⟩ hbound
  change i.val≤10 at hbound
  by_cases hp : i.val<10
  · have hb : i < 10#usize := by scalar_tac
    let j := Usize.wrapping_add 16#usize i
    have hj : j.val=16+i.val := PV_B3P_Offset226V3.add_value 16#usize i
      (by have hsize := usize_1024_size; change 16+i.val < _; omega)
    obtain ⟨q,hq⟩ := selected_claim_total claims 0#usize j (by change 0<3; omega) (by omega)
    obtain ⟨w1,hw1⟩ := update w i q (by change i.val<10; omega)
    let next := Usize.wrapping_add i 1#usize
    have hn : next.val=i.val+1 := PV_B3P_Offset226V3.add_value i 1#usize
      (by have hsize := usize_1024_size; change i.val+1 < _; omega)
    simp only [j] at hq
    refine ⟨.cont (w1,next),?_,?_,?_⟩
    · simp only [reference_terminal.composition_parts_loop0.body,mask_columns10,c1_columns16,
        hb,↓reduceIte,lift,bind_tc_ok,hq,hw1,next]
    · change next.val≤10
      omega
    · change 10-next.val<10-i.val
      omega
  · have hb : ¬i<10#usize := by scalar_tac
    refine ⟨.done w,?_,True.intro⟩
    simp only [reference_terminal.composition_parts_loop0.body,mask_columns10,hb,↓reduceIte]

#print axioms mask_columns10
#print axioms c1_columns16
#print axioms mask_loop_total
end PV_B3P_Success227
