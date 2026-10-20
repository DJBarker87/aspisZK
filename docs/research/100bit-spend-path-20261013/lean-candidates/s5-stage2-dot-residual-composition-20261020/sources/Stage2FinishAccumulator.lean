import Stage2FinishPairing
import HchecksAccumulator
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Stage2FinishAccumulator
open AspisR1Stage2 AspisCircleGroupOrder
variable {K F W : Type} [Field K] [Fintype K] [Algebra (ZMod P) K]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod P) F]

/-- S5 (EbyKDot) interpretation, kept separate from S8's restored/finalized
batched weights. This law states only what a returned dot product means. -/
def DotLaw (ops : Stage2Finish.FinishOps W) (decode : Stage2Finish.E → F)
    (iota : K →+* F) (v : verifier.View) (a : verifier.Accumulator)
    (d : MatchingSupport.Data F) (weights : Fin 64 → K) : Prop :=
  ∀ value, ops.dot v.final_message (alloc.vec.Vec.deref a.weights) = ok (.Ok value) →
    decode value = ∑ l : Fin 64, d.f l * iota (weights l)

/-- S8/R15 accumulator invariant on the very state consumed by finish.
The first ten terms require checkpoint provenance; the remaining twelve
require the source query/weight traversal and the R13 leaf correspondence. -/
structure Invariant (decode : Stage2Finish.E → F) (iota : K →+* F)
    (a : verifier.Accumulator) (d : MatchingSupport.Data F)
    (q : Fin 22 → Fin 262144) (rho : K) (weights : Fin 64 → K) : Prop where
  weights : ∀ l, weights l = ∑ j : Fin 22, rho ^ j.val * QueryResidualBridge.basis (K := K) q j l
  rhs : decode a.rhs = ∑ j : Fin 22, (iota rho) ^ j.val * QueryResidualBridge.values d q j

/-- The final comparison supplies the exact closed sum and residualBatch
field; neither the closed sum nor residualBatch is a premise. -/
theorem finish_closedSum (ops : Stage2Finish.FinishOps W)
    (decode : Stage2Finish.E → F) (compare : Stage2FinishPairing.ComparisonLaw ops decode)
    (iota : K →+* F) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
    (d : MatchingSupport.Data F) (q : Fin 22 → Fin 262144) (rho : K)
    (weights : Fin 64 → K) (dot : DotLaw ops decode iota v a d weights)
    (inv : Invariant decode iota a d q rho weights)
    (two : ops.folds p.variant = ok 2#usize)
    (h : Stage2Finish.verifier.finishRelationWithOps ops v p a obs = ok (.Ok ())) :
    HchecksAccumulator.ClosedSum iota d q rho := by
  obtain ⟨alpha0,claim0,alpha1,claim1,ws,alphas,pair,actual,
    ha0,hr0,ha1,hr1,hw,has,hp,hpc,hd,hn,hdc⟩ := Stage2Finish.finish_success ops v p a obs two h
  have heq : (∑ l : Fin 64, d.f l * iota (weights l)) =
      ∑ j : Fin 22, (iota rho) ^ j.val * QueryResidualBridge.values d q j :=
    (dot actual hd).symm.trans ((compare actual a.rhs hdc).trans inv.rhs)
  have closed : HchecksAccumulator.ClosedSum iota d q rho := by
    unfold HchecksAccumulator.ClosedSum
    simpa only [inv.weights] using heq
  exact closed


theorem finish_residualBatch (ops : Stage2Finish.FinishOps W)
    (decode : Stage2Finish.E → F) (compare : Stage2FinishPairing.ComparisonLaw ops decode)
    (iota : K →+* F) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
    (d : MatchingSupport.Data F) (q : Fin 22 → Fin 262144) (rho : K)
    (weights : Fin 64 → K) (dot : DotLaw ops decode iota v a d weights)
    (inv : Invariant decode iota a d q rho weights)
    (two : ops.folds p.variant = ok 2#usize)
    (h : Stage2Finish.verifier.finishRelationWithOps ops v p a obs = ok (.Ok ())) :
    ∑ j : Fin 22, (iota rho) ^ j.val * QueryResidualBridge.residuals d q j = 0 := by
  exact HchecksAccumulator.residual_of_closed_sum iota d q rho
    (finish_closedSum ops decode compare iota v p a obs d q rho weights dot inv two h)

#print axioms finish_closedSum
#print axioms finish_residualBatch
end AspisR1.Stage2FinishAccumulator
end
