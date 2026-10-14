import R1BackgroundOutputMap

/-! A deterministic output map commutes with the independent-answer law. -/
set_option autoImplicit false
namespace AspisR1.BackgroundLawMap

open R0C.V3 FS

theorem blaw_map {I A X C D : Type} [DecidableEq I] [Inhabited A]
    [Fintype A] (f : C → D) (g : X → List A → C) (obs : D → ℚ)
    (own : BS I A X) (pend : List (I × Option A)) :
    blaw (fun x as => f (g x as)) obs own pend =
      blaw g (fun c => obs (f c)) own pend := by
  induction own generalizing pend with
  | done x => rfl
  | ask i k ih =>
      simp only [blaw]
      apply mean_congr
      intro a
      exact ih a pend
  | spawn c nxt ih =>
      simp only [blaw]
      exact ih (pend ++ [(c, none)])

#print axioms blaw_map

end AspisR1.BackgroundLawMap
