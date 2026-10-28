import NDO_JGn_CopyNumeric
import NDO_JGl_ConcreteSelected
import RPu_FIw_WordValue
import RPv_FIr_ArrayRead
set_option autoImplicit false
namespace AspisR1.JGn_SelectedHelper
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_semantic_terminal

theorem value (selected : Array field.QM31 84#usize) (h : field.QM31)
    (gather : array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy
      JGl_SelectedCells.builder field.QM31.ZERO JFu_TerminalCallback.claims=ok selected)
    (run : selected_claim selected 0#usize 26#usize=ok h) : h=JGn_CopyNumeric.helper := by
  have same := JGl_ConcreteSelected.value selected gather
  rw [same] at run
  unfold selected_claim at run
  rw [JFu_SelectedClaim.stride,bind_tc_ok] at run
  obtain ⟨p,hp,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨i,hi,run⟩ := FIv_Map.bind_success _ _ _ run
  have vp := FIw_WordValue.mul 0#usize 28#usize p hp
  have vi := FIw_WordValue.add p 26#usize i hi
  change p.val=0 at vp
  change i.val=p.val+26 at vi
  have index : i.val=26 := by omega
  have slot := FIr_ArrayRead.slot JGl_ConcreteSelected.data i h run
  rw [index] at slot
  change some JGn_CopyNumeric.helper=some h at slot
  exact (Option.some.inj slot).symm
#print axioms value
end AspisR1.JGn_SelectedHelper
