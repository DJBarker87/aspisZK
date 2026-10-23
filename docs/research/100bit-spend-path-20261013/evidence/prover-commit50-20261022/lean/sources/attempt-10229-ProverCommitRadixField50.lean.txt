import R1Z.ProverCommitRadixTop50
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitRadixField50
variable {K : Type} [Field K]
theorem top (f : Nat → K) (x : K) (n : Nat) :
    ProverCommitRadix50.block f x n*(x^4)^n+ProverCommitRadix50.blocks f x n=
      (ProverCommitInterpolationPoly48.poly (4*(n+1)) f).eval x := by
  exact ProverCommitRadixTop50.top f x n
#print axioms top
end R1Z.ProverCommitRadixField50
