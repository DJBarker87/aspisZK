import NDO_JGj_MatrixLoopTotal
import NDO_JGj_ExternalTailLoopTotal
import RPv_FJb_ColumnBound
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_ExternalTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical)
open FJb_MatrixGroupStep (State)
theorem source (s : State) (hs : canonical s) :
    ∃ out,state_only_poseidon.external_linear_lazy s=ok out ∧ canonical out := by
  obtain ⟨stage,rs,cs⟩ := JGj_MatrixLoopTotal.source 4 0#usize s rfl hs
  obtain ⟨sums,rt⟩ := FJb_BuilderTotal.value 4#usize
    (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64) FJb_ColumnTable.callback
    (Array.repeat 4#usize 0#u64) stage (by intro i hi;exact FJb_ColumnTable.callback_total stage i hi)
  have hb := FJb_ColumnBound.value stage sums rt
  obtain ⟨out,ro,co⟩ := JGj_ExternalTailLoopTotal.source 16 0#usize stage sums rfl cs hb
  refine ⟨out,?_,co⟩
  unfold state_only_poseidon.external_linear_lazy
  rw [rs,bind_tc_ok]
  change (do
    let sums ← array_from_fn_copy 4#usize
      (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64) FJb_ColumnTable.callback
      (Array.repeat 4#usize 0#u64) stage
    state_only_poseidon.external_linear_lazy_loop1 stage sums 0#usize)=ok out
  rw [rt,bind_tc_ok,ro]
#print axioms source
end AspisR1.JGj_ExternalTotal
end
