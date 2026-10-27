import RPv_FIy_ScalingSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_ScalingNonvacuity
open Aeneas Aeneas.Std Result FIq_Native
open FIy_IteratorTraversal
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical decoded)

theorem zero : ∃ out : Array QM 33#usize,
    FIy_ScaleReadback.run (Array.repeat 33#usize field.QM31.ZERO) field.QM31.ZERO=ok out ∧ canonical out := by
  have hc : canonical (Array.repeat 33#usize field.QM31.ZERO) := by
    intro x hx
    have he : x=field.QM31.ZERO := List.eq_of_mem_replicate hx
    rw [he]
    exact FIv_NativeValue.zero.1
  obtain ⟨out,hr,hcanon,_⟩ := FIy_Scaling.total _ _ hc FIv_NativeValue.zero.1
  exact ⟨out,hr,hcanon⟩
#print axioms zero
end AspisR1.FIy_ScalingNonvacuity
end
