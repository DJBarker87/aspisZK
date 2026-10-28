import PV_B3P_HostSuccess227
import PV_B3P_E227_13
import PV_B3P_Offset226V3
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem usize_mul_value (i j : Usize)
    (h : i.val*j.val < UScalar.size .Usize) :
    (Usize.wrapping_mul i j).val = i.val*j.val := by
  rw [Usize.wrapping_mul_val_eq,Nat.mod_eq_of_lt h]

theorem expand_inner_total {N : Usize}
    (weights : Array aspis_core.field.QM31 N)
    (prepared : host_terminal_field.PreparedQm31Multiplier) (index : Usize)
    (hi : 2*index.val ≤ N.val) :
    Success (reference_copy_terminal.Selectors.expand_loop0_loop0 weights prepared index) := by
  unfold reference_copy_terminal.Selectors.expand_loop0_loop0
  refine loop_total _ (fun x : Array aspis_core.field.QM31 N × Usize => x.2.val)
    (fun x => 2*x.2.val ≤ N.val) ?_ (weights,index) hi
  rintro ⟨w,i⟩ hbound
  change 2*i.val ≤ N.val at hbound
  by_cases hp : 0 < i.val
  · have hb : i > 0#usize := by scalar_tac
    let j := Usize.wrapping_sub i 1#usize
    have hj : j.val = i.val-1 := PV_B3P_Offset226V3.sub_value i 1#usize (by scalar_tac)
    have hN : N.val < UScalar.size .Usize := by simpa only [UScalar.size] using N.hBounds
    let k := Usize.wrapping_mul 2#usize j
    have hk : k.val = 2*j.val := usize_mul_value 2#usize j (by change 2*j.val < _; omega)
    let k1 := Usize.wrapping_add k 1#usize
    have hk1 : k1.val = k.val+1 := PV_B3P_Offset226V3.add_value k 1#usize (by change k.val+1 < _; omega)
    obtain ⟨parent,hparent⟩ := PV_B3P_Success227.index w j (by omega)
    obtain ⟨right,hright⟩ := total_host_terminal_field_PreparedQm31Multiplier_mul prepared parent
    obtain ⟨left,hleft⟩ := qsub parent right
    obtain ⟨w1,hw1⟩ := update w k left (by omega)
    obtain ⟨w2,hw2⟩ := update w1 k1 right (by omega)
    simp only [j,k,k1] at hparent hw1 hw2
    refine ⟨.cont (w2,j),?_,?_,?_⟩
    · simp only [reference_copy_terminal.Selectors.expand_loop0_loop0.body,hb,
        ↓reduceIte,lift,bind_tc_ok,hparent,hright,hleft,hw1,hw2]
    · omega
    · omega
  · have hb : ¬ i > 0#usize := by scalar_tac
    refine ⟨.done w,?_,True.intro⟩
    simp only [reference_copy_terminal.Selectors.expand_loop0_loop0.body,hb,↓reduceIte]

#print axioms usize_mul_value
#print axioms expand_inner_total
end PV_B3P_Success227
