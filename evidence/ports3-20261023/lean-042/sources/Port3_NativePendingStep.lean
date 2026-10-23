import Port3_NativePendingBody

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativePendingStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativePendingBody

/-- One current emitted while-loop step, with its actual slice read and Vec
back closure. All four widening casts are the native extracted casts. -/
theorem step (weights : Slice aspis_core.field.QM31) (raw : alloc.vec.Vec Row)
    (index : Usize) (wsize : weights.val.length=64) (rsize : raw.val.length=64)
    (active : index.val<64) :
    ∃ w, Slice.index_usize weights index=ok w ∧
      body weights raw index = ok (.cont
        (raw.set index (Port3_PendingInstall.row w),Usize.wrapping_add index 1#usize)) := by
  obtain ⟨w,hr,_⟩ := WP.spec_imp_exists
    (Slice.index_usize_spec weights index (by rw [wsize]; exact active))
  obtain ⟨⟨old,back⟩,hmut,_,hback⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec raw index (by change index.val<raw.val.length; rw [rsize]; exact active))
  have hm : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Row) raw index=ok (old,back) := by
    rw [alloc.vec.Vec.index_mut_slice_index]
    exact hmut
  have cond : index<Slice.len weights := by change index.val<weights.val.length; omega
  refine ⟨w,hr,?_⟩
  simp only [body,if_pos cond,hr,hm,hback,lift,bind_tc_ok]
  rfl

/-- Widening and back-writing keep the raw Vec's exact length. -/
theorem step_length (weights : Slice aspis_core.field.QM31) (raw : alloc.vec.Vec Row)
    (index : Usize) (after : alloc.vec.Vec Row) (next : Usize)
    (wsize : weights.val.length=64) (rsize : raw.val.length=64) (active : index.val<64)
    (success : body weights raw index=ok (.cont (after,next))) :
    after.val.length=64 ∧ next.val=index.val+1 := by
  obtain ⟨w,_,run⟩ := step weights raw index wsize rsize active
  have same := ControlFlow.cont.inj (Result.ok.inj (run.symm.trans success))
  have he := Prod.mk.inj same
  rw [← he.1,← he.2]
  exact ⟨by simpa using rsize,Port3_Wrapping.increment index (by omega)⟩

#print axioms Port3_NativePendingBody.body
#print axioms Port3_NativePendingBody.run
#print axioms Port3_NativePendingBody.extracted
#print axioms step
#print axioms step_length
end AspisR1.Port3_NativePendingStep
end
