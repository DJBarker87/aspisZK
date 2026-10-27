import BEh_Scope
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEk_LawFields
open Aeneas Aeneas.Std Result SdkC_Source
open BEg_Observation BEh_Scope

/-- Exact observable fields of the success-conditioned boundary. Rejected
error kinds and rejected mutable states do not enter this characterization. -/
theorem accepted_eq {S A E F : Type} (native : Outcome S A E) (source : Outcome S A F)
    (law : Law native source) : accepted native.1 = accepted source.1 := by
  cases h : accepted native.1 with
  | none => exact (law.2.1.mp h).symm
  | some a =>
    exact ((accepted_iff source.1 a).mpr ((law.1.1 a).mp ((accepted_iff native.1 a).mp h))).symm

theorem exact_fields {S A E F : Type} (native : Outcome S A E) (source : Outcome S A F) :
    Law native source ↔
    accepted native.1 = accepted source.1 ∧ native.2.2 = source.2.2 ∧
    (∀ a, native.1 = ok (.Ok a) → native.2.1 = source.2.1) := by
  constructor
  · intro law
    exact ⟨accepted_eq native source law,logs native source law,
      fun a yes => congrArg Prod.fst (law.1.2 a yes)⟩
  · rintro ⟨values,history,carrier⟩
    refine ⟨⟨?_,?_⟩,⟨?_,fun _ => history⟩⟩
    · intro a
      rw [←accepted_iff,←accepted_iff,values]
    · intro a yes
      exact Prod.ext (carrier a yes) history
    · rw [values]

#print axioms accepted_eq
#print axioms exact_fields
end AspisR1.BEk_LawFields
end
