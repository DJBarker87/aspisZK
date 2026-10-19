import AspisV8R19.AdaptiveFirstReadLaw

/-! A fail-visible wrapper that stops before a memo-table cache hit.

The guarded program is branch-wise fresh by construction, so its lazy
memoized law is exactly the independent-answer interpreter.  This is not an
equivalence with the unguarded source program: proving that a source run does
not reach the guard, or charging the probability that it does, remains a
separate obligation. -/
set_option autoImplicit false
namespace AspisV8R19.GuardedFirstRead
open AspisV8PairedCommitment
open MemoizedProgramLaw AdaptiveFirstReadLaw OracleResampling
variable {I A O : Type}
noncomputable section

def guardFresh [DecidableEq I] :
    Program I A O → Table I A → Program I A (Option O)
  | .done o, _ => .done (some o)
  | .ask i next, t =>
      match t i with
      | some _ => .done none
      | none => .ask i (fun a => guardFresh (next a) (put t i a))

def mapSome : Program I A O → Program I A (Option O)
  | .done o => .done (some o)
  | .ask i next => .ask i (fun a => mapSome (next a))

theorem guardFresh_fresh [DecidableEq I] (p : Program I A O) (t : Table I A) :
    FreshFrom (guardFresh p t) t := by
  induction p generalizing t with
  | done o => trivial
  | ask i next ih =>
      cases h : t i with
      | none =>
          simp only [guardFresh, h, FreshFrom, true_and]
          exact fun a => ih a (put t i a)
      | some a =>
          simp only [guardFresh, h, FreshFrom]

theorem guardFresh_eq_mapSome [DecidableEq I] (p : Program I A O)
    (t : Table I A) (fresh : FreshFrom p t) :
    guardFresh p t = mapSome p := by
  induction p generalizing t with
  | done o => rfl
  | ask i next ih =>
      simp only [FreshFrom] at fresh
      simp only [guardFresh, fresh.1, mapSome]
      congr 1
      funext a
      exact ih a (put t i a) (fresh.2 a)

theorem guarded_lazy_eq_independentMean [Fintype A] [DecidableEq I]
    (p : Program I A O) (t : Table I A)
    (observe : View I A (Option O) → ℚ) :
    lazyMean (guardFresh p t) t observe =
      independentMean (guardFresh p t) observe :=
  lazyMean_eq_independentMean (guardFresh p t) t
    (guardFresh_fresh p t) observe

#print axioms guardFresh_fresh
#print axioms guardFresh_eq_mapSome
#print axioms guarded_lazy_eq_independentMean
end
end AspisV8R19.GuardedFirstRead
