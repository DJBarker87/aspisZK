import SameBodyQueryClaimExact
import TypedRelationTerminalV3

/-! DRAFT: exact compact-response arithmetic interfaces only.
The existing same-word forward evaluator is identified with the historical
sourceHorner recurrence. No terminal-success or desired game equation is
assumed. The final covector/public-input construction remains independent.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
namespace AspisV8Completion.SameBodyCompactTerminal
open SameBodyQueryClaimExact
open scoped BigOperators
variable {K : Type*} [Field K] [DecidableEq K]

def parts (m : SameBodyRelation.Sent K) : AspisV8.OptimizedRelationRefinement.Sent K :=
  ⟨m 0,m 1,m 2,m 3,m 4,m 5⟩

/-- Seven coefficients only: the omitted c4 is reconstructed from the
incoming scalar. No 1024-entry weight or concrete extension field is reduced. -/
theorem compact_to_sourceHorner (quarter claim alpha : K) (m : SameBodyRelation.Sent K) :
    (ringArithmetic quarter).evaluate7
      (SameBodyRelation.compact (ringArithmetic quarter).toArithmetic claim m) alpha =
    AspisV8.OptimizedRelationRefinement.sourceHorner quarter claim (parts m) alpha := by
  simp [ringArithmetic,SameBodyRelation.compact,parts,
    AspisV8.OptimizedRelationRefinement.sourceHorner,List.ofFn_succ]
  ring

theorem afterQuery_sourceHorner (quarter ordinary alpha rho : K)
    (word : SameBodyRelation.Word K) (opened : Fin 22 → K) :
    SameBodyQueryClaim.afterQuery (ringArithmetic quarter) word ordinary alpha rho opened =
      AspisV8.OptimizedRelationRefinement.sourceHorner quarter ordinary
        (parts (SameBodyRelation.response word 0)) alpha +
      ∑ i : Fin 22, rho^(i.val+1)*opened i := by
  unfold SameBodyQueryClaim.afterQuery
  rw [injectClaim_exact,compact_to_sourceHorner]

/-- All three later messages are projected from the actual word; this does
not choose constant-body callbacks or move later messages before challenges. -/
theorem terminalClaim_sourceHorner (quarter initial : K)
    (word : SameBodyRelation.Word K) (coins : Fin 3 → K) :
    SameBodyQueryClaim.terminalClaim (ringArithmetic quarter) word coins initial =
      AspisV8.OptimizedRelationRefinement.sourceHorner quarter
        (AspisV8.OptimizedRelationRefinement.sourceHorner quarter
          (AspisV8.OptimizedRelationRefinement.sourceHorner quarter initial
            (parts (SameBodyRelation.response word 1)) (coins 0))
          (parts (SameBodyRelation.response word 2)) (coins 1))
        (parts (SameBodyRelation.response word 3)) (coins 2) := by
  unfold SameBodyQueryClaim.terminalClaim
  rw [compact_to_sourceHorner,compact_to_sourceHorner,compact_to_sourceHorner]

#print compact_to_sourceHorner
#print axioms compact_to_sourceHorner
#print axioms afterQuery_sourceHorner
#print axioms terminalClaim_sourceHorner
end AspisV8Completion.SameBodyCompactTerminal
