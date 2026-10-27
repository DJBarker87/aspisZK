import RPu_FIx_ScheduleValue
import RPu_FIx_PreweightedMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_SchedulePacked
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
open FIx_ScheduleValue (Public Openings Selectors)

theorem value (packed out : Array NQ 24#usize) (pub : Public) (o : Openings) (s : Selectors)
    (hp : canonical packed) (hz : canonical o.z) (hh : canonical s.high) (hl : canonical s.low)
    (success : pool_v1.pair_forest_semantic_terminal.add_schedule_lanes packed pub o s=ok out) :
    canonical out ∧ ∀ j : Fin (24#usize).val,
      decoded out j=decoded packed j+
        FIx_SelectedMeaning.contribution (FIx_ScheduleModel.initial pub.variant s o) 0 j.val+
        FIx_SelectedMeaning.contribution (FIx_ScheduleModel.absorption pub.variant s o) 16 j.val := by
  unfold pool_v1.pair_forest_semantic_terminal.add_schedule_lanes at success
  obtain ⟨⟨initial,absorption⟩,hparts,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨middle,hmiddle,success⟩ := FIv_Map.bind_success _ _ _ success
  have parts := FIx_ScheduleValue.value pub o s initial absorption hz hh hl hparts
  have first := FIx_PreweightedMeaning.value packed middle 0#usize initial
    (FIx_ScheduleModel.initial pub.variant s o) parts.2.2.1 (by decide) (by decide) hp parts.1 hmiddle
  have second := FIx_PreweightedMeaning.value middle out 16#usize absorption
    (FIx_ScheduleModel.absorption pub.variant s o) parts.2.2.2 (by decide) (by decide) first.1 parts.2.1 success
  refine ⟨second.1,?_⟩
  intro j
  rw [second.2 j,first.2 j]
  rfl
#print axioms value
end AspisR1.FIx_SchedulePacked
end
