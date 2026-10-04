import AspisV8R19.OracleProgramOps

/-! Exact first-read reduction for causal shared-oracle programs.

The next address and stopping time may depend on all previous answers.  The
`FreshFrom` premise says only that every reached address is absent from the
memoization table at the instant it is queried.  Under that premise the lazy
memoized interpreter is exactly the interpreter that samples an independent
uniform answer at every query.  No future transcript value is conditioned on,
and cache hits are not resampled.

This is a generic oracle-program theorem.  Establishing `FreshFrom` (or
accounting for its failure) for the complete Aspis source experiment remains a
separate source-specific obligation. -/
set_option autoImplicit false
namespace AspisV8R19.AdaptiveFirstReadLaw
open MemoizedProgramLaw OracleProgramOps OracleResampling
open AspisV8PairedCommitment
variable {I A O R : Type}

def FreshFrom [DecidableEq I] : Program I A O → Table I A → Prop
  | .done _, _ => True
  | .ask i next, t => t i = none ∧ ∀ a, FreshFrom (next a) (put t i a)

noncomputable def independentMean [Fintype A] :
    Program I A O → (View I A O → ℚ) → ℚ
  | .done o, observe => observe ([],o)
  | .ask i next, observe =>
      mean (fun a => independentMean (next a)
        (fun r => observe ((i,a)::r.1,r.2)))

theorem lazyMean_eq_independentMean [Fintype A] [DecidableEq I]
    (p : Program I A O) (t : Table I A) (fresh : FreshFrom p t)
    (observe : View I A O → ℚ) :
    lazyMean p t observe = independentMean p observe := by
  induction p generalizing t observe with
  | done o => rfl
  | ask i next ih =>
      have missing : t i = none := fresh.1
      rw [lazyMean, missing]
      simp only [independentMean]
      apply mean_congr
      intro a
      exact ih a (put t i a) (fresh.2 a) _

theorem complete_oracle_eq_independentMean [Fintype I] [Fintype A]
    [Nonempty A] [DecidableEq I] (p : Program I A O) (t : Table I A)
    (fresh : FreshFrom p t) (observe : View I A O → ℚ) :
    mean (fun H => observe (eval (complete t H) p)) = independentMean p observe := by
  rw [exact_oracle_law p t observe]
  exact lazyMean_eq_independentMean p t fresh observe

theorem empty_oracle_eq_independentMean [Fintype I] [Fintype A]
    [Nonempty A] [DecidableEq I] (p : Program I A O)
    (fresh : FreshFrom p (fun _ => none)) (observe : View I A O → ℚ) :
    mean (fun H => observe (eval H p)) = independentMean p observe := by
  rw [empty_oracle_law p observe]
  exact lazyMean_eq_independentMean p (fun _ => none) fresh observe

theorem independentMean_bind [Fintype A] (p : Program I A O)
    (next : O → Program I A R) (observe : View I A R → ℚ) :
    independentMean (bind p next) observe =
      independentMean p (fun first =>
        independentMean (next first.2) (fun second =>
          observe (first.1 ++ second.1,second.2))) := by
  induction p generalizing observe with
  | done o => rfl
  | ask i k ih =>
      change mean (fun a => independentMean (bind (k a) next)
        (fun r => observe ((i,a)::r.1,r.2))) =
        mean (fun a => independentMean (k a) (fun first =>
          independentMean (next first.2) (fun second =>
            observe (((i,a)::first.1) ++ second.1,second.2))))
      apply mean_congr
      intro a
      simpa only [List.cons_append] using
        ih a (fun r => observe ((i,a)::r.1,r.2))

theorem squeezeProgram_fresh_iff [DecidableEq I]
    (i j : I) (next : A → A → Program I A O) (t : Table I A) :
    FreshFrom (.ask i (fun a => .ask j (next a))) t ↔
      t i = none ∧ ∀ a, (put t i a) j = none ∧ ∀ b, FreshFrom (next a b) (put (put t i a) j b) := by
  rfl

#print axioms lazyMean_eq_independentMean
#print axioms complete_oracle_eq_independentMean
#print axioms empty_oracle_eq_independentMean
#print axioms independentMean_bind
#print axioms squeezeProgram_fresh_iff
end AspisV8R19.AdaptiveFirstReadLaw
