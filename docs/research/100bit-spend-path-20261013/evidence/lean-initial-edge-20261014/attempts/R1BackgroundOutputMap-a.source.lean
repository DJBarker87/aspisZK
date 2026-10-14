import R0C.V3.BS

/-! Mapping a pure output function commutes with background-sampler follow. -/
set_option autoImplicit false
namespace AspisR1.BackgroundOutputMap

open R0C.V3

section
variable {I A X C D : Type} [DecidableEq I] [Inhabited A]

theorem finished_map (f : C → D) (g : X → List A → C)
    (own : BS I A X) (pend : List (I × Option A)) :
    finished (fun x as => f (g x as)) own pend = (finished g own pend).map f := by
  cases own with
  | done x => simp [finished]
  | ask i k => rfl
  | spawn c nxt => rfl

theorem bfollow_map (f : C → D) (g : X → List A → C) :
    ∀ (tr : List (I × A)) (own : BS I A X)
      (pend : List (I × Option A)) (T : Table I A),
      bfollow (fun x as => f (g x as)) tr own pend T =
        (bfollow g tr own pend T).map f := by
  intro tr
  induction tr with
  | nil =>
      intro own pend T
      simp [bfollow, finished_map]
  | cons q rest ih =>
      rcases q with ⟨l, a⟩
      intro own pend T
      simp only [bfollow, finished_map]
      cases hf : finished g (pushSpawns own pend).1 (pushSpawns own pend).2 with
      | none =>
          simp only [hf, Option.map_none]
          split <;> simp_all [ih]
      | some c =>
          simp [hf]

#print axioms finished_map
#print axioms bfollow_map

end
end AspisR1.BackgroundOutputMap
