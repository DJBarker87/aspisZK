import R1Z.ProverCommitEncoderPhi53
import R1FirstFold
/-! The source inverse transform uses exactly the payload model's stored
circle slot order. This algebraic bridge makes no native node-table claim. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEncoderPhiModel53

theorem phi_radix {K : Type} [Field K] (x y : K) (h : Fin 4 → K) :
    ProverCommitEncoderPhi53.phi x y h=
      AspisV5FriConcreteEncoderCommutation.radix4Evaluate y (-y) x h := by
  funext i
  fin_cases i <;>
    simp only [ProverCommitEncoderPhi53.phi,AspisV5FriConcreteEncoderCommutation.radix4Evaluate,
      Matrix.cons_val_zero,Matrix.cons_val_succ] <;> ring

theorem phi_fibre {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K]
    (u : Fin 262144) (h : Fin 4 → K) :
    ProverCommitEncoderPhi53.phi (AspisWide.FinalEncoder.exactCircleX u)
      (AspisWide.FinalEncoder.exactCircleY u) h=AspisR1.FirstFold.fibreEvaluate u h := by
  exact phi_radix _ _ _

#print axioms phi_radix
#print axioms phi_fibre
end R1Z.ProverCommitEncoderPhiModel53
