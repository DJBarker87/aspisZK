import NNU_QueryInduction
set_option autoImplicit false
namespace AspisR1.NNY_LoopTransport
open Aeneas Aeneas.Std Result ControlFlow
/-- Least-fixed-point transport from single source iterations. Rejected
terminal results need no equality; every continued state is transported. -/
theorem accepted {S T : Type} (left right : S → Result (ControlFlow S T))
 (Good : T → Prop)
 (step : ∀ s r, left s=ok r →
   match r with
   | cont t => right s=ok (.cont t)
   | done out => Good out → right s=ok (.done out))
 (s : S) (out : T) (good : Good out) (run : loop left s=ok out) :
 loop right s=ok out := by
 have aux : ∀ s, loop left s=div ∨
   ∀ out, Good out → loop left s=ok out → loop right s=ok out := by
  apply loop.fixpoint_induct left
   (motive := fun f => ∀ s, f s=div ∨ ∀ out, Good out → f s=ok out → loop right s=ok out)
  · apply Lean.Order.admissible_pi_apply
     (fun s (r : Result T) => r=div ∨ ∀ out, Good out → r=ok out → loop right s=ok out)
    intro s
    exact Lean.Order.admissible_flatOrder _ (Or.inl rfl)
  · intro f ih s
    dsimp only
    cases hb : left s with
    | fail e => right; intro out _ he; simp only [hb] at he; cases he
    | div => exact Or.inl (by simp only [hb])
    | ok r =>
      cases r with
      | done value =>
        right
        intro out hg he
        simp only [hb] at he
        cases he
        rw [loop.eq_def]
        simp only [step s (.done value) hb hg]
      | cont next =>
        rcases ih next with hd | hp
        · exact Or.inl (by simpa only [hb] using hd)
        · right
          intro out hg he
          rw [loop.eq_def]
          simp only [step s (.cont next) hb]
          exact hp out hg (by simpa only [hb] using he)
 rcases aux s with hd | hp
 · rw [hd] at run; cases run
 · exact hp out good run
#print axioms accepted
end AspisR1.NNY_LoopTransport
