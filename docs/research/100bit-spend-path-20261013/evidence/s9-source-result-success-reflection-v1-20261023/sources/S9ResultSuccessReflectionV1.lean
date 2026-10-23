import S9SourceResultTransportV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ResultSuccessReflectionV1

abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

/-- A mapped successful result comes from a successful value in this same run. -/
theorem mapResult_ok_iff {A B : Type} (f : A → B) (r : Result A) (b : B) :
    mapResult f r = .ok b ↔ ∃ a, r = .ok a ∧ f a = b := by
  cases r with
  | ok a =>
    constructor
    · intro h
      exact ⟨a, rfl, Result.ok.inj h⟩
    · rintro ⟨a', h, hb⟩
      have he : a = a' := Result.ok.inj h
      subst a'
      exact congrArg Result.ok hb
  | fail e => simp only [mapResult, AspisR1S9SourceResultTransportV1.mapResult]; simp
  | div => simp only [mapResult, AspisR1S9SourceResultTransportV1.mapResult]; simp

/-- Transfer totality and a semantic output predicate along a complete Result map. -/
theorem source_success_of_target {A B : Type} (f : A → B)
    (source : Result A) (target : Result B) (P : B → Prop)
    (hmap : mapResult f source = target)
    (htarget : ∃ b, target = .ok b ∧ P b) :
    ∃ a, source = .ok a ∧ P (f a) := by
  obtain ⟨b, hb, hp⟩ := htarget
  obtain ⟨a, ha, hab⟩ := (mapResult_ok_iff f source b).mp (hmap.trans hb)
  refine ⟨a, ha, ?_⟩
  rw [hab]
  exact hp

#print axioms mapResult_ok_iff
#print axioms source_success_of_target

end AspisR1S9ResultSuccessReflectionV1
