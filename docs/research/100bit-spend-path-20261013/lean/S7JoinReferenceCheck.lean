import S7JoinAccumulatorReference

/-! Abstract check interface so specializing the exact tower never unfolds
its large field dictionaries or the accumulator recurrence. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S7JoinReferenceCheck
open AspisCircleGroupOrder
variable {K E : Type} [Field K] [Fintype K] [DecidableEq K]
  [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) K] [Algebra (ZMod P) E]

def check (iota : K →+* E) (data : MatchingSupport.Data E)
    (q : Fin 22 → Fin 262144) (rho : K) : Prop :=
  let s := S7JoinAccumulatorReference.run iota data q rho
  (∑ l : Fin 64, data.f l*iota (s.weights l))=s.rhs

theorem check_iff (iota : K →+* E) (data : MatchingSupport.Data E)
    (q : Fin 22 → Fin 262144) (rho : K) :
    check iota data q rho ↔ HchecksAccumulator.ClosedSum iota data q rho := by
  unfold check
  exact S7JoinAccumulatorReference.check_iff_closed_sum iota data q rho

#print axioms check_iff
end AspisR1.S7JoinReferenceCheck
