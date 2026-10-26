import BEg_Observation
import BEg_Continuation
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEg_Events
open Aeneas Aeneas.Std Result SdkC_Source
open BEg_Observation

/-- Any failure event defined on accepted output and retained effects is
unchanged pointwise. No distribution, work metric or query loss is altered.
The native source observation equality must be proved separately. -/
theorem event {S A E F : Type}
    (left : Result (core.result.Result A E) × S × Log)
    (right : Result (core.result.Result A F) × S × Log)
    (same : observe left = observe right) (failure : Option A × S × Log → Prop) :
    failure (observe left) ↔ failure (observe right) := by rw [same]

/-- Exact logs give exact occurrence accounting; error erasure contributes
zero additional issued calls, not merely an upper bound. -/
theorem accounting {S A E F : Type}
    (left : Result (core.result.Result A E) × S × Log)
    (right : Result (core.result.Result A F) × S × Log)
    (same : observe left = observe right) :
    left.2.2 = right.2.2 ∧ left.2.2.length = right.2.2.length ∧
      SdkC_Source.readLog left.2.2 = SdkC_Source.readLog right.2.2 := by
  have effects := congrArg (fun out : Option A × S × Log => out.2) same
  have logs := congrArg (fun out : S × Log => out.2) effects
  exact ⟨logs,congrArg List.length logs,congrArg SdkC_Source.readLog logs⟩

#print axioms event
#print axioms accounting
end AspisR1.BEg_Events
end
