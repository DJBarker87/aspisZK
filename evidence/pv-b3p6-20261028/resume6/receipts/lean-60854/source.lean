import PV_B3P_HostSuccess227
import PV_B3P_P227_13a
import PV_B3P_Offset226V3
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem reverse1_total (semantic : Array aspis_core.field.QM31 24#usize)
    (prepared : host_terminal_field.PreparedQm31Multiplier)
    (composition : aspis_core.field.QM31) (index : Usize)
    (hi : index.val ≤ 24) : Success (reference_terminal.composition_parts_loop1 semantic prepared composition index) := by
  unfold reference_terminal.composition_parts_loop1
  refine loop_total _ (fun x : aspis_core.field.QM31 × Usize => x.2.val)
    (fun x => x.2.val ≤ 24) ?_ (composition,index) hi
  rintro ⟨acc,i⟩ hbound
  by_cases hp : 0 < i.val
  · have hb : i > 0#usize := by scalar_tac
    let j := Usize.wrapping_sub i 1#usize
    have hj : j.val = i.val-1 := PV_B3P_Offset226V3.sub_value i 1#usize (by scalar_tac)
    obtain ⟨mulval,hmul⟩ := total_host_terminal_field_PreparedQm31Multiplier_mul prepared acc
    obtain ⟨readval,hread⟩ := PV_B3P_Success227.index semantic j (by change j.val < 24; omega)
    obtain ⟨next,hnext⟩ := qadd mulval readval
    refine ⟨.cont (next,j),?_,?_,?_⟩
    · simp only [reference_terminal.composition_parts_loop1.body,hb,↓reduceIte,lift,bind_tc_ok,hmul,
        reference_terminal.read227,hread,hnext]
    · dsimp only
      omega
    · dsimp only
      omega
  · have hb : ¬ i > 0#usize := by scalar_tac
    refine ⟨.done acc,?_,True.intro⟩
    simp only [reference_terminal.composition_parts_loop1.body,hb,↓reduceIte]

#print axioms reverse1_total

theorem reverse2_total (poseidon : Array aspis_core.field.QM31 4#usize)
    (prepared : host_terminal_field.PreparedQm31Multiplier)
    (composition : aspis_core.field.QM31) (index : Usize)
    (hi : index.val ≤ 4) : Success (reference_terminal.composition_parts_loop2 poseidon prepared composition index) := by
  unfold reference_terminal.composition_parts_loop2
  refine loop_total _ (fun x : aspis_core.field.QM31 × Usize => x.2.val)
    (fun x => x.2.val ≤ 4) ?_ (composition,index) hi
  rintro ⟨acc,i⟩ hbound
  by_cases hp : 0 < i.val
  · have hb : i > 0#usize := by scalar_tac
    let j := Usize.wrapping_sub i 1#usize
    have hj : j.val = i.val-1 := PV_B3P_Offset226V3.sub_value i 1#usize (by scalar_tac)
    obtain ⟨mulval,hmul⟩ := total_host_terminal_field_PreparedQm31Multiplier_mul prepared acc
    obtain ⟨readval,hread⟩ := PV_B3P_Success227.index poseidon j (by change j.val < 4; omega)
    obtain ⟨next,hnext⟩ := qadd mulval readval
    refine ⟨.cont (next,j),?_,?_,?_⟩
    · simp only [reference_terminal.composition_parts_loop2.body,hb,↓reduceIte,lift,bind_tc_ok,hmul,
        reference_terminal.read227,hread,hnext]
    · dsimp only
      omega
    · dsimp only
      omega
  · have hb : ¬ i > 0#usize := by scalar_tac
    refine ⟨.done acc,?_,True.intro⟩
    simp only [reference_terminal.composition_parts_loop2.body,hb,↓reduceIte]

#print axioms reverse2_total
end PV_B3P_Success227
