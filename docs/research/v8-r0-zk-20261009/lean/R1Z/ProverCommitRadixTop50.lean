import R1Z.ProverCommitRadix50
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitRadixTop50
variable {K : Type} [CommRing K]
theorem top (f : Nat → K) (x : K) (n : Nat) :
    ProverCommitRadix50.block f x n*(x^4)^n+ProverCommitRadix50.blocks f x n=
      (ProverCommitInterpolationPoly48.poly (4*(n+1)) f).eval x := by
  rw [← ProverCommitRadix50.blocks_poly,ProverCommitRadix50.blocks]
  exact add_comm _ _
#print axioms top
end R1Z.ProverCommitRadixTop50
