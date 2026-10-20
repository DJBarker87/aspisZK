import R1QueryResidualBridge

/-! Keep the accumulator interface abstract until after its algebraic
composition, avoiding normalization of concrete tower instances. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.HchecksAccumulator
open AspisCircleGroupOrder
variable {K E : Type} [Field K] [Fintype K]
  [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod P) E] [Algebra (ZMod P) K]

def ClosedSum (iota : K →+* E) (data : MatchingSupport.Data E)
    (q : Fin 22 → Fin 262144) (rho : K) : Prop :=
  (∑ l : Fin 64, data.f l * iota
    (∑ j : Fin 22, rho ^ j.val * QueryResidualBridge.basis (K := K) q j l)) =
  ∑ j : Fin 22, (iota rho) ^ j.val * QueryResidualBridge.values data q j

theorem residual_of_closed_sum (iota : K →+* E) (data : MatchingSupport.Data E)
    (q : Fin 22 → Fin 262144) (rho : K) (h : ClosedSum iota data q rho) :
    ∑ j : Fin 22, (iota rho) ^ j.val * QueryResidualBridge.residuals data q j = 0 := by
  exact QueryResidualBridge.accumulated_equation_implies_residual_batch iota data q rho h

#print axioms residual_of_closed_sum
end AspisR1.HchecksAccumulator
end
