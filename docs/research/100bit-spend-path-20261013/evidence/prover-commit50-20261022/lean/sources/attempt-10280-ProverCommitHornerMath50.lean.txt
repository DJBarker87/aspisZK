import R1Z.ProverCommitRadix50
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitHornerMath50
variable {K : Type} [Field K]

theorem eval_succ (f : Nat → K) (x : K) (n : Nat) :
    (ProverCommitInterpolationPoly48.poly (n+1) f).eval x=
      (ProverCommitInterpolationPoly48.poly n f).eval x+f n*x^n := by
  rw [ProverCommitRadix50.eval_poly,ProverCommitRadix50.eval_poly,Finset.sum_range_succ]

theorem top (f : Nat → K) (x : K) (n : Nat) :
    f n*x^n+(ProverCommitInterpolationPoly48.poly n f).eval x=
      (ProverCommitInterpolationPoly48.poly (n+1) f).eval x := by
  rw [eval_succ]
  exact add_comm _ _

#print axioms eval_succ
#print axioms top
end R1Z.ProverCommitHornerMath50
