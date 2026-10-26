import BEf_ExtractionGap
import BEg_Observation
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEg_D188Accepted
open Aeneas Aeneas.Std Result

/-- Success-conditioning alone cannot identify a carrier erased by a value
interface. This is an inhabited interface countermodel, not shipped Rust. -/
theorem successful_value_does_not_determine_effects :
    ∃ (left right : Unit → Bool → Result (core.result.Result Unit Unit) × Bool),
      (∀ input state, (left input state).1 = .ok (.Ok ()) ∧
        (right input state).1 = .ok (.Ok ())) ∧
      (∀ input state, BEg_Observation.accepted (left input state).1 =
        BEg_Observation.accepted (right input state).1) ∧
      (left () false).2 ≠ (right () false).2 := by
  refine ⟨(fun _ state => (.ok (.Ok ()),state)),
    (fun _ state => (.ok (.Ok ()),!state)),?_,?_,?_⟩
  · intro _ _; exact ⟨rfl,rfl⟩
  · intro _ _; rfl
  · change false ≠ true
    decide

#print axioms successful_value_does_not_determine_effects
end AspisR1.BEg_D188Accepted
end
