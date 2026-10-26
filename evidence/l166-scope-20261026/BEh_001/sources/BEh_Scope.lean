import BEg_Observation
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEh_Scope
open Aeneas Aeneas.Std Result SdkC_Source

abbrev Outcome (S A E : Type) := Result (core.result.Result A E) × S × Log

/-- Accepted outputs, observable mutable carrier and every attempted read agree.
S is a COMMON projection of concrete carriers, not an assertion of pointer equality. -/
def AcceptedPath {S A E F : Type} (native : Outcome S A E) (source : Outcome S A F) : Prop :=
  (∀ a, native.1 = .ok (.Ok a) ↔ source.1 = .ok (.Ok a)) ∧
  (∀ a, native.1 = .ok (.Ok a) → native.2 = source.2)

/-- Rejection kinds and rejected final mutable states may differ. Ordered attempted
histories (including a failed final syscall) must still be associated. -/
def RejectedPrefix {S A E F : Type} (native : Outcome S A E) (source : Outcome S A F) : Prop :=
  (BEg_Observation.accepted native.1 = none ↔ BEg_Observation.accepted source.1 = none) ∧
  (BEg_Observation.accepted native.1 = none → native.2.2 = source.2.2)

def Law {S A E F : Type} (native : Outcome S A E) (source : Outcome S A F) : Prop :=
  AcceptedPath native source ∧ RejectedPrefix native source

/-- Quantifier-complete two-slot local requirement. Input must contain the SAME
reached proof, Prepared/query/root, borrowed slices and native state; admission
must be derived at its actual prefix. This is a specification, not an instance. -/
def BothSlots {I S A E F : Type}
    (admitted : I → Fin 2 → S → Prop)
    (native : I → Fin 2 → S → Log → Outcome S A E)
    (source : I → Fin 2 → S → Log → Outcome S A F) : Prop :=
  ∀ input slot state before, admitted input slot state →
    Law (native input slot state before) (source input slot state before)

/-- BEg's observation equality is sufficient; its rejected-state equality is
stronger than the success-conditioned ruling requires. -/
theorem of_observe {S A E F : Type} (native : Outcome S A E) (source : Outcome S A F)
    (same : BEg_Observation.observe native = BEg_Observation.observe source) : Law native source := by
  have values := congrArg Prod.fst same
  have effects : native.2 = source.2 := congrArg Prod.snd same
  refine ⟨⟨?_,fun _ _ => effects⟩,⟨?_,fun _ => congrArg Prod.snd effects⟩⟩
  · intro a
    rw [← BEg_Observation.accepted_iff, ← BEg_Observation.accepted_iff]
    exact Iff.of_eq (congrArg (fun x => x = some a) values)
  · exact Iff.of_eq (congrArg (fun x => x = none) values)

theorem reflexive {S A E : Type} (out : Outcome S A E) : Law out out :=
  ⟨⟨fun _ => Iff.rfl,fun _ _ => rfl⟩,⟨Iff.rfl,fun _ => rfl⟩⟩

/-- Full ordered log association follows, without requiring rejected state equality. -/
theorem logs {S A E F : Type} (native : Outcome S A E) (source : Outcome S A F)
    (law : Law native source) : native.2.2 = source.2.2 := by
  cases h : BEg_Observation.accepted native.1 with
  | none => exact law.2.2 h
  | some a => exact congrArg Prod.snd (law.1.2 a ((BEg_Observation.accepted_iff _ _).mp h))

#print axioms of_observe
#print axioms reflexive
#print axioms logs
end AspisR1.BEh_Scope
end
