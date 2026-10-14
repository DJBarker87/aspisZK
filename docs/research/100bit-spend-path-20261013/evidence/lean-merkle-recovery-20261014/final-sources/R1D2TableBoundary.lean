import FS2.Statement
import AspisV8R19.R572SequentialWordMass

/-! An interface audit: FS2.D2 charges a deterministic escape caused by a
change of table at probability one. This is not an impossibility theorem
for knowledge extraction; it rules out silently reusing this premise for
a classifier whose table change alone makes every next challenge good. -/
set_option autoImplicit false
namespace AspisR1.D2TableBoundary

open FS FS2 AspisV8PairedCommitment
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.R572SequentialWordMass

variable {X M C W Pf I A : Type} [DecidableEq I] [Inhabited A]
  [Fintype A] [Nonempty A]

theorem table_flip_cost (pr : Protocol X M C W Pf I A)
    (rb : RoundByRound' X M C I A) (hD2 : D2 pr rb)
    (i : Nat) (P : Prefix X M C) (m : M) (before after : Table I A)
    (hround : P.round = i) (hi : i < pr.r)
    (hbefore : rb.doomed P before)
    (hafter : ∀ c : C, ¬ rb.doomed (P.ext m c) after) :
    (1 : ℚ) ≤ rb.ε i := by
  have h := hD2 i P m before after hround hi hbefore
  have hone : independentMean (pr.samp i P m).toProgram
      (fun v => indicator (¬ rb.doomed (P.ext m v.2) after)) = 1 := by
    calc
      _ = independentMean (pr.samp i P m).toProgram (fun _ => (1 : ℚ)) := by
        apply independentMean_congr
        intro v
        simp only [indicator, if_pos (hafter v.2)]
      _ = 1 := independentMean_const _ _
  rw [hone] at h
  exact h

#print axioms table_flip_cost

end AspisR1.D2TableBoundary
