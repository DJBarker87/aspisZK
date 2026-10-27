import RPt_BEf_Bind
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEg_Observation
open Aeneas Aeneas.Std Result SdkC_Source

/-- The approved success-conditioned observation. Outer failure, divergence,
and inner Err are rejected; an accepted value is retained in full. -/
def accepted {A E : Type} : Result (core.result.Result A E) → Option A
  | .ok (.Ok a) => some a
  | _ => none

def observe {S A E : Type} (out : Result (core.result.Result A E) × S × Log) :
    Option A × S × Log := (accepted out.1,out.2)

theorem accepted_iff {A E : Type} (out : Result (core.result.Result A E)) (a : A) :
    accepted out = some a ↔ out = .ok (.Ok a) := by
  cases out with
  | fail e => simp [accepted]
  | div => simp [accepted]
  | ok value => cases value with
    | Err e => simp [accepted]
    | Ok b => simp [accepted]

theorem same_success {S A E F : Type}
    (left : Result (core.result.Result A E) × S × Log)
    (right : Result (core.result.Result A F) × S × Log)
    (same : observe left = observe right) (a : A)
    (success : left.1 = .ok (.Ok a)) :
    right.1 = .ok (.Ok a) ∧ left.2 = right.2 := by
  have value := congrArg Prod.fst same
  have effects := congrArg Prod.snd same
  exact ⟨(accepted_iff right.1 a).mp (by simpa only [observe,success,accepted] using value.symm), effects⟩

theorem same_rejection {S A E F : Type}
    (left : Result (core.result.Result A E) × S × Log)
    (right : Result (core.result.Result A F) × S × Log)
    (same : observe left = observe right) :
    (accepted left.1 = none ↔ accepted right.1 = none) ∧ left.2 = right.2 := by
  exact ⟨by rw [show accepted left.1 = accepted right.1 from congrArg Prod.fst same],
    congrArg Prod.snd same⟩

#print axioms accepted_iff
#print axioms same_success
#print axioms same_rejection
end AspisR1.BEg_Observation
end
