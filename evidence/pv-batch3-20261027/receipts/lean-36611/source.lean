import PV_B3_MaskSparseStates
namespace PV_B3_MaskSparse67
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134
open PV_B3_SparseArray PV_B3_MaskSparseStep PV_B3_MaskSparseStates
set_option autoImplicit false
theorem link134 : Array.index_usize host_forest.MASK_LINKS 134#usize = ok (1006#u16,908#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer134 : P134 1006 = 0#u8 := by rfl
theorem consumer134 : C134 908 = 0#u8 := by rfl
theorem step134 : body s134 = ok (cont s135) := by
  apply step P134 C134 M134 134#usize 1006#usize 908#usize 1006#u16 908#u16 1#u8 1#u8
    (by decide) link134 (by rfl) (by rfl) (by decide) (by decide)
    (by rw [producer134]; rfl) (by rw [consumer134]; rfl) (by decide) (by decide)
theorem link135 : Array.index_usize host_forest.MASK_LINKS 135#usize = ok (1006#u16,896#u16) := by
  unfold host_forest.MASK_LINKS
  rfl
-- Only a single sparse count is reduced; neither an array nor a run is evaluated.
theorem producer135 : P135 1006 = 1#u8 := by rfl
theorem consumer135 : C135 896 = 0#u8 := by rfl
theorem step135 : body s135 = ok (cont s136) := by
  apply step P135 C135 M135 135#usize 1006#usize 896#usize 1006#u16 896#u16 2#u8 1#u8
    (by decide) link135 (by rfl) (by rfl) (by decide) (by decide)
    (by rw [producer135]; rfl) (by rw [consumer135]; rfl) (by decide) (by decide)
theorem finish : run s136 = ok (.Ok (array 64#usize M136)) := by
  unfold run
  rw [loop.eq_def]
  change (do let cf ← body s136; match cf with
    | .cont t => loop body t
    | .done value => ok value) = _
  have hd : body s136 = ok (done (.Ok (array 64#usize M136))) := by
    unfold body s136 host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop.body
    rw [if_neg (by decide)]
  rw [hd]
  rfl
theorem suffix : run s134 = ok (.Ok (array 64#usize M136)) :=
  (run_next _ _ step134).trans ((run_next _ _ step135).trans finish)
#print axioms link134
#print axioms producer134
#print axioms consumer134
#print axioms step134
#print axioms link135
#print axioms producer135
#print axioms consumer135
#print axioms step135
#print axioms finish
#print axioms suffix
end PV_B3_MaskSparse67
