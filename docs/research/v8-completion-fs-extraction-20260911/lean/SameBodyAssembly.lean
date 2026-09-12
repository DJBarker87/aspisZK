import SemanticWireExecution
import SameBodyOrdinary
set_option autoImplicit false
namespace AspisV8Completion.SameBodyAssembly
universe u v
variable {K : Type u} {Schedule : Type v}
open SameBodyRelation

def early (w : Word K) : Fin 417 → K := fun i => w ⟨i.val, by omega⟩

/-- Later relation serialization preserves every earlier consumed value for
EVERY legal continuation. No equality with a separately supplied program is
a premise. This is not an adversary/source or ROM-distribution coupling. -/
theorem produced_early (w : Word K) (strategy : Strategy K Schedule)
    (tau alpha : K) (queries : Schedule) (rho : K) (coins : Fin 3 → K)
    (i : Fin 697) (h : i.val < 417) :
    produce (early w) strategy tau alpha queries rho coins i = w i := by
  unfold produce
  have fixed := assembled_early (early w)
    (roundsOfTail (strategy tau).response0
      (((strategy tau).afterAlpha0 alpha).afterQueries queries rho) coins)
    ((strategy tau).afterAlpha0 alpha).final256 ⟨i.val,h⟩
  simpa [early] using fixed

theorem preserves_semantic (ops : SemanticWireExecution.Arithmetic K)
    (w : Word K) (strategy : Strategy K Schedule) (z : Fin 10 → K)
    (tau alpha : K) (queries : Schedule) (rho : K) (coins : Fin 3 → K) :
    SemanticWireExecution.terminalInput ops
      (produce (early w) strategy tau alpha queries rho coins) z =
      SemanticWireExecution.terminalInput ops w z := by
  apply SemanticWireExecution.suffix_independent
  intro i hi
  exact produced_early w strategy tau alpha queries rho coins i (by omega)

/-- Both successful preparation and inverse/domain rejection are preserved.
The OOD candidates and gamma/kappa are legitimately fixed before this suffix.
Their actual transcript derivation is still a separate source obligation. -/
theorem preserves_ordinary [DecidableEq K] (ops : SameBodyOrdinary.Arithmetic K)
    (w : Word K) (strategy : Strategy K Schedule)
    (gamma kappa tau alpha : K) (p0 p1 : SameBodyOrdinary.Point K)
    (queries : Schedule) (rho : K) (coins : Fin 3 → K) :
    SameBodyOrdinary.prepare ops
      (produce (early w) strategy tau alpha queries rho coins) gamma kappa p0 p1 =
      SameBodyOrdinary.prepare ops w gamma kappa p0 p1 := by
  obtain ⟨hc, ho, hi⟩ := SameBodyOrdinary.consumed_fields_fixed
    (produce (early w) strategy tau alpha queries rho coins) w
    (fun i _ h => produced_early w strategy tau alpha queries rho coins i h)
  have hs : SameBodyOrdinary.rowScalar ops
      (produce (early w) strategy tau alpha queries rho coins) gamma kappa =
      SameBodyOrdinary.rowScalar ops w gamma kappa := by
    simp only [SameBodyOrdinary.rowScalar, hc, hi]
  simp only [SameBodyOrdinary.prepare, ho, hs]

#print preserves_semantic
#print preserves_ordinary
#print axioms produced_early
#print axioms preserves_semantic
#print axioms preserves_ordinary
end AspisV8Completion.SameBodyAssembly
