import R1Z.ProverCommitTerminalMath51
/-! Generic head split prevents concrete tower instance reduction at the caller. -/
set_option autoImplicit false
namespace R1Z.ProverCommitTerminalHead51
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

theorem exact_value (a b : Nat → K) :
    ProverCommitTerminalMath51.factor (a 0) (b 0)*ProverCommitTerminalMath51.product a b 9 1=
      R0P.SemSource.eqValue (fun i : Fin 10 => a i.val) (fun i : Fin 10 => b i.val) := by
  have h := ProverCommitTerminalMath51.product_model a b
  rw [ProverCommitTerminalMath51.product] at h
  exact h

#print axioms exact_value
end R1Z.ProverCommitTerminalHead51
