import AspisV8R19.AdaptiveFirstReadLaw

/-! A bounded, fixed-tape presentation of independent oracle execution.

`Within p n` is an all-branches bound: a terminal program fits every tape
length, while an ask fits one larger tape exactly when every continuation fits
the remaining length.  `evalTape` consumes only the answers reached by the
program; the unused suffix of its tape is intentionally ghost data.

This is a generic finite-program factorization lemma.  It makes no claim
about a source implementation or about any security property. -/
set_option autoImplicit false
namespace AspisV8R19.IndependentMeanFixedTape

open MemoizedProgramLaw OracleResampling
open AspisV8R19.AdaptiveFirstReadLaw

variable {I A O : Type}

inductive Within : Program I A O → Nat → Type where
  | done (o : O) (n : Nat) : Within (.done o) n
  | ask (i : I) (next : A → Program I A O) (n : Nat)
      (h : ∀ a, Within (next a) n) : Within (.ask i next) (n + 1)

def headTailEquiv (n : Nat) : (Fin (n + 1) → A) ≃ A × (Fin n → A) where
  toFun tape := (tape 0, fun j => tape j.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv tape := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · rfl
  right_inv p := by
    cases p
    rfl

def evalTape {p : Program I A O} {n : Nat}
    (within : Within p n) (tape : Fin n → A) : View I A O :=
  match p, within with
  | .done o, .done _ _ => ([], o)
  | .ask i next, .ask _ _ m h =>
      let split := headTailEquiv (A := A) m tape
      let tail := evalTape (h split.1) split.2
      ((i, split.1) :: tail.1, tail.2)

@[simp] theorem evalTape_done (I : Type) (o : O) (n : Nat)
    (tape : Fin n → A) :
    evalTape (@Within.done I A O o n) tape = ([], o) := rfl

@[simp] theorem evalTape_ask (I : Type) (i : I) (next : A → Program I A O)
    (m : Nat) (h : ∀ a, Within (next a) m)
    (a : A) (tail : Fin m → A) :
    evalTape (@Within.ask I A O i next m h)
      ((headTailEquiv (A := A) m).symm (a, tail)) =
      ((i, a) :: (evalTape (h a) tail).1, (evalTape (h a) tail).2) := by
  rfl

theorem mean_evalTape_eq_independentMean [Fintype A] [Nonempty A]
    (p : Program I A O) (n : Nat) (within : Within p n)
    (observe : View I A O → ℚ) :
    mean (fun tape : Fin n → A => observe (evalTape within tape)) =
      independentMean p observe := by
  induction p generalizing n observe with
  | done o =>
      cases within with
      | done _ m =>
          simp only [evalTape_done, independentMean]
          exact mean_const _
  | ask i next ih =>
      cases within with
      | ask _ _ m hnext =>
          let e := headTailEquiv (A := A) m
          calc
            mean (fun tape : Fin (m + 1) → A =>
                observe (evalTape (Within.ask i next m hnext) tape)) =
                mean (fun q : A × (Fin m → A) =>
                  observe (evalTape (Within.ask i next m hnext) (e.symm q))) := by
                    simpa only [Equiv.symm_apply_apply] using
                      (mean_equiv e (fun q : A × (Fin m → A) =>
                        observe (evalTape (Within.ask i next m hnext) (e.symm q))))
            _ = mean (fun q : A × (Fin m → A) =>
                  observe ((i, q.1) :: (evalTape (hnext q.1) q.2).1,
                    (evalTape (hnext q.1) q.2).2)) := by
                    apply mean_congr
                    intro q
                    cases q with
                    | mk a tail =>
                        exact congrArg observe
                          (evalTape_ask I i next m hnext a tail)
            _ = mean (fun a : A => mean (fun tail : Fin m → A =>
                  observe ((i, a) :: (evalTape (hnext a) tail).1,
                    (evalTape (hnext a) tail).2))) := by
                    exact mean_prod (X := A) (Y := Fin m → A)
                      (fun a tail => observe
                        ((i, a) :: (evalTape (hnext a) tail).1,
                          (evalTape (hnext a) tail).2))
            _ = mean (fun a : A =>
                  independentMean (next a)
                    (fun r => observe ((i, a) :: r.1, r.2))) := by
                    apply mean_congr
                    intro a
                    rw [ih a m (hnext a)
                      (fun r => observe ((i, a) :: r.1, r.2))]
            _ = independentMean (.ask i next) observe := by
                    rfl

#print axioms mean_evalTape_eq_independentMean

end AspisV8R19.IndependentMeanFixedTape
