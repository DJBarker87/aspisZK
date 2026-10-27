import FJh_InternalLinearExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_LinearNonvacuity
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (State CanonicalState cell)
/-- Constructive native internal-linear success on a canonical symbolic zero
array; no concrete recurrence is evaluated. -/
theorem value : ∃ out : State,
    state_only_poseidon.internal_linear_lazy (Array.repeat 16#usize field.QM31.ZERO)=ok out ∧
    CanonicalState out := by
  have hc : CanonicalState (Array.repeat 16#usize field.QM31.ZERO) := by
    intro i
    simpa only [cell,Array.repeat,List.getElem_replicate] using FIv_NativeValue.zero.1
  obtain ⟨out,run,cout,_⟩ := FJh_InternalLinearExact.source_success _ hc
  exact ⟨out,run,cout⟩
#print axioms value
end AspisR1.FJh_LinearNonvacuity
end
