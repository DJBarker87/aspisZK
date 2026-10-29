import PV_B3P_ExpandSuccess227
import PV_B3P_RefFieldSuccess227
import PV_B3P_E227_19
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem slice_read {α : Type} (xs : Slice α) (i : Usize)
    (hi : i.val < (Slice.len xs).val) : Success (Slice.index_usize xs i) := by
  obtain ⟨q,hq,_⟩ := WP.spec_imp_exists
    (Slice.index_usize_spec xs i (by simpa only [Slice.len_val] using hi))
  exact ⟨q,hq⟩

#print axioms slice_read

theorem host_pack_loop_total (values : Slice aspis_core.field.QM31)
    (padded : Array aspis_core.field.QM31 4#usize) (index : Usize)
    (hlen : (Slice.len values).val ≤ 4) (hi : index.val ≤ (Slice.len values).val) :
    Success (host_terminal_field.qm31_pack_base4_loop values padded index) := by
  unfold host_terminal_field.qm31_pack_base4_loop
  refine loop_total _ (fun x : Array aspis_core.field.QM31 4#usize × Usize =>
      (Slice.len values).val-x.2.val)
    (fun x => x.2.val ≤ (Slice.len values).val) ?_ (padded,index) hi
  rintro ⟨w,i⟩ hbound
  change i.val ≤ (Slice.len values).val at hbound
  by_cases hp : i.val < (Slice.len values).val
  · have hb : i < Slice.len values := by scalar_tac
    obtain ⟨q,hq⟩ := slice_read values i hp
    obtain ⟨w1,hw1⟩ := update w i q (by change i.val<4; omega)
    let j := Usize.wrapping_add i 1#usize
    have hj : j.val=i.val+1 := PV_B3P_Offset226V3.add_value i 1#usize (by
      have h := usize_ten_size
      change i.val+1 < _
      omega)
    refine ⟨.cont (w1,j),?_,?_,?_⟩
    · simp only [host_terminal_field.qm31_pack_base4_loop.body,hb,↓reduceIte,lift,bind_tc_ok,hq,hw1,j]
    · change j.val ≤ (Slice.len values).val
      omega
    · change (Slice.len values).val-j.val < (Slice.len values).val-i.val
      omega
  · have hb : ¬ i < Slice.len values := by scalar_tac
    refine ⟨.done w,?_,True.intro⟩
    simp only [host_terminal_field.qm31_pack_base4_loop.body,hb,↓reduceIte]

#print axioms host_pack_loop_total

theorem ref_pack_loop_total (values : Slice aspis_core.field.QM31)
    (padded : Array aspis_core.field.QM31 4#usize) (index : Usize)
    (hlen : (Slice.len values).val ≤ 4) (hi : index.val ≤ (Slice.len values).val) :
    Success (reference_field.qm31_pack_base4_loop values padded index) := by
  unfold reference_field.qm31_pack_base4_loop
  refine loop_total _ (fun x : Array aspis_core.field.QM31 4#usize × Usize =>
      (Slice.len values).val-x.2.val)
    (fun x => x.2.val ≤ (Slice.len values).val) ?_ (padded,index) hi
  rintro ⟨w,i⟩ hbound
  change i.val ≤ (Slice.len values).val at hbound
  by_cases hp : i.val < (Slice.len values).val
  · have hb : i < Slice.len values := by scalar_tac
    obtain ⟨q,hq⟩ := slice_read values i hp
    obtain ⟨w1,hw1⟩ := update w i q (by change i.val<4; omega)
    let j := Usize.wrapping_add i 1#usize
    have hj : j.val=i.val+1 := PV_B3P_Offset226V3.add_value i 1#usize (by
      have h := usize_ten_size
      change i.val+1 < _
      omega)
    refine ⟨.cont (w1,j),?_,?_,?_⟩
    · simp only [reference_field.qm31_pack_base4_loop.body,hb,↓reduceIte,lift,bind_tc_ok,hq,hw1,j]
    · change j.val ≤ (Slice.len values).val
      omega
    · change (Slice.len values).val-j.val < (Slice.len values).val-i.val
      omega
  · have hb : ¬ i < Slice.len values := by scalar_tac
    refine ⟨.done w,?_,True.intro⟩
    simp only [reference_field.qm31_pack_base4_loop.body,hb,↓reduceIte]

#print axioms ref_pack_loop_total
end PV_B3P_Success227
