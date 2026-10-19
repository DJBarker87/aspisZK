import RRProgramMeanTools

noncomputable section
namespace AspisR1.RRProgramAbortBound
open AspisR1.RRProgramTraversal AspisR1.RRProgramMeanTools
open AspisR1.SequentialProgramInvariants AspisR1.CompPolyFactorMeanTools
open AspisV8R19.MemoizedProgramLaw
variable {I A K S : Type} [Fintype A] [Nonempty A]

def childMass (mass : S → Nat) (cs : List (K × S)) : Nat :=
  (cs.map (fun child => mass child.2)).sum

/-- The union bound follows the executed short-circuiting list traversal;
unreached siblings contribute only an upper bound, never a success premise. -/
theorem walkChildren_abort_le (run : S → Program I A (Option (List (List K))))
    (mass : S → Nat) (δ : ℚ) (hδ : 0 ≤ δ)
    (hrun : ∀ s, outMean (run s) abortIndicator ≤ (mass s : ℚ)*δ)
    (cs : List (K × S)) :
    outMean (walkChildren run cs) abortIndicator ≤ (childMass mass cs : ℚ)*δ := by
  induction cs with
  | nil => simp [walkChildren, outMean, childMass, abortIndicator]
  | cons head tail ih =>
    rcases head with ⟨a,s⟩
    have hB : 0 ≤ (childMass mass tail : ℚ)*δ := by positivity
    calc
      _ ≤ outMean (run s) abortIndicator + (childMass mass tail : ℚ)*δ := by
        apply optionBind_abort_le _ _ _ hB
        intro ys
        rw [mapOption_abort_mean]
        exact ih
      _ ≤ (mass s : ℚ)*δ + (childMass mass tail : ℚ)*δ :=
        add_le_add (hrun s) (le_refl _)
      _ = (childMass mass ((a,s)::tail) : ℚ)*δ := by
        simp only [childMass, List.map_cons, List.sum_cons, Nat.cast_add]
        ring

/-- A depth-d adaptive RR traversal aborts with probability at most
d * initial_mass * δ. Each actual local root sampler must supply its abort
bound; each successful child list must preserve the multiplicity potential.
No fixed branching order, global good-tape event, or work credit is assumed. -/
theorem collectProgram_abort_le (zeroTest : S → Bool)
    (children : S → Program I A (Option (List (K × S))))
    (mass : S → Nat) (δ : ℚ) (hδ : 0 ≤ δ)
    (hlocal : ∀ s, outMean (children s) abortIndicator ≤ (mass s : ℚ)*δ)
    (hmass : ∀ s, AllOutcomes (children s) (fun out =>
      ∀ cs, out = some cs → childMass mass cs ≤ mass s))
    (d : Nat) (s : S) :
    outMean (collectProgram zeroTest children d s) abortIndicator ≤
      (d : ℚ)*(mass s : ℚ)*δ := by
  induction d generalizing s with
  | zero =>
    change abortIndicator (some _) ≤ (0 : ℚ)*_ * _
    simp [abortIndicator]
  | succ d ih =>
    have hB : 0 ≤ (d : ℚ)*(mass s : ℚ)*δ := by positivity
    have hnext : AllOutcomes (children s) (fun out => ∀ cs, out = some cs →
        outMean (walkChildren (collectProgram zeroTest children d) cs) abortIndicator ≤
          (d : ℚ)*(mass s : ℚ)*δ) := by
      apply all_mono _ (hmass s)
      intro out ho cs hcs
      have hchild := ho cs hcs
      calc
        _ ≤ (childMass mass cs : ℚ)*((d : ℚ)*δ) := by
          apply walkChildren_abort_le _ mass _ (by positivity)
          intro u
          calc
            _ ≤ (d : ℚ)*(mass u : ℚ)*δ := ih u
            _ = (mass u : ℚ)*((d : ℚ)*δ) := by ring
        _ ≤ (mass s : ℚ)*((d : ℚ)*δ) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hchild) (by positivity)
        _ = (d : ℚ)*(mass s : ℚ)*δ := by ring
    calc
      _ ≤ outMean (children s) abortIndicator + (d : ℚ)*(mass s : ℚ)*δ :=
        optionBind_abort_le_on_outcomes (children s) _ _ hB hnext
      _ ≤ (mass s : ℚ)*δ + (d : ℚ)*(mass s : ℚ)*δ :=
        add_le_add (hlocal s) (le_refl _)
      _ = ((d+1 : Nat) : ℚ)*(mass s : ℚ)*δ := by
        rw [Nat.cast_add, Nat.cast_one]
        ring

#print axioms childMass
#print axioms walkChildren_abort_le
#print axioms collectProgram_abort_le
end AspisR1.RRProgramAbortBound
