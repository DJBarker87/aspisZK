import PV_B3P_ClaimSuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem interval_loop_total (high : Array aspis_core.field.QM31 64#usize)
    (end1 : Usize) (sum : aspis_core.field.QM31) (initial : Usize)
    (he : end1.val≤64) (hi : initial.val≤end1.val) :
    Success (reference_terminal.sum_interval227_loop high end1 sum initial) := by
  unfold reference_terminal.sum_interval227_loop
  refine loop_total _ (fun x : aspis_core.field.QM31 × Usize => end1.val-x.2.val)
    (fun x => x.2.val≤end1.val) ?_ (sum,initial) hi
  rintro ⟨acc,i⟩ hbound
  change i.val≤end1.val at hbound
  by_cases hp : i.val<end1.val
  · have hb : i<end1 := by scalar_tac
    obtain ⟨q,hq⟩ := index high i (by change i.val<64; omega)
    obtain ⟨acc1,hacc1⟩ := qadd acc q
    let next := Usize.wrapping_add i 1#usize
    have hn : next.val=i.val+1 := PV_B3P_Offset226V3.add_value i 1#usize
      (by have hsize := usize_1024_size; change i.val+1 < _; omega)
    refine ⟨.cont (acc1,next),?_,?_,?_⟩
    · simp only [reference_terminal.sum_interval227_loop.body,hb,↓reduceIte,
        reference_terminal.read227,lift,bind_tc_ok,hq,hacc1,next]
    · change next.val≤end1.val
      omega
    · change end1.val-next.val<end1.val-i.val
      omega
  · have hb : ¬i<end1 := by scalar_tac
    refine ⟨.done acc,?_,True.intro⟩
    simp only [reference_terminal.sum_interval227_loop.body,hb,↓reduceIte]

theorem interval_total (high : Array aspis_core.field.QM31 64#usize)
    (sum : aspis_core.field.QM31) (start end1 : Usize)
    (he : end1.val≤64) (hi : start.val≤end1.val) :
    Success (reference_terminal.sum_interval227 high sum start end1) :=
  interval_loop_total high end1 sum start he hi

theorem poseidon_selectors_total (selectors : reference_copy_terminal.Selectors) :
    Success (reference_terminal.poseidon_selectors selectors) := by
  unfold reference_terminal.poseidon_selectors
  apply bind
  · exact interval_total selectors.high _ 0#usize 57#usize (by change 57≤64; omega)
      (by change 0≤57; omega)
  intro q
  exact ok _

#print axioms interval_loop_total
#print axioms interval_total
#print axioms poseidon_selectors_total
end PV_B3P_Success227
