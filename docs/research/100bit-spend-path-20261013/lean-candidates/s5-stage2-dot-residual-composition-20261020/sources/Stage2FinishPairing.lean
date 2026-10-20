import Stage2FinishControl
import R1LiteralPairingChecks
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Stage2FinishPairing
open AspisR1Stage2
open AspisCircleGroupOrder
variable {F W : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod P) F]

/-- Field/decoder frontiers: interpretation of the actual reads, quarter scaling,
and polynomial evaluator. This is a backend law, not an accepted-pairing premise. -/
structure RoundLaws (ops : AspisR1Stage2.Stage2Finish.FinishOps W) (decode : AspisR1Stage2.Stage2Finish.E → F)
    (bytes : Slice U8) (poly : Polynomial F) : Prop where
  boundary : ∀ c0 c4 lhs,
    ops.field bytes 0#usize = ok c0 → ops.field bytes 4#usize = ok c4 →
    ops.add c0 c4 = ok lhs → decode lhs = TwoRoundComparison.boundary poly
  quarter : ∀ m claim rhs, ops.quarter = ok m → ops.mulM claim m = ok rhs →
    decode rhs = RoundPairing.quarter * decode claim
  eval : ∀ alpha value, ops.polynomial bytes alpha = ok value →
    decode value = poly.eval (decode alpha)

/-- Comparison soundness is only needed after successful source comparisons. -/
def ComparisonLaw (ops : AspisR1Stage2.Stage2Finish.FinishOps W) (decode : AspisR1Stage2.Stage2Finish.E → F) : Prop :=
  ∀ x y, ops.ne x y = ok false → decode x = decode y

theorem round_refines (ops : AspisR1Stage2.Stage2Finish.FinishOps W) (decode : AspisR1Stage2.Stage2Finish.E → F)
    (compare : ComparisonLaw ops decode) (bytes : Slice U8) (poly : Polynomial F)
    (laws : RoundLaws ops decode bytes poly) (alpha claim out : AspisR1Stage2.Stage2Finish.E) (round : Usize)
    (h : AspisR1Stage2.Stage2Finish.verifier.finishRelationRoundWithOps ops bytes alpha claim round = ok (.Ok out)) :
    TwoRoundComparison.boundary poly = RoundPairing.quarter * decode claim ∧
    decode out = poly.eval (decode alpha) := by
  obtain ⟨c0,c4,lhs,m,rhs,hc0,hc4,hlhs,hm,hrhs,hne,heval⟩ :=
    AspisR1Stage2.Stage2Finish.round_success ops bytes alpha claim out round h
  exact ⟨(laws.boundary c0 c4 lhs hc0 hc4 hlhs).symm.trans
    ((compare lhs rhs hne).trans (laws.quarter m claim rhs hm hrhs)),
    laws.eval alpha out heval⟩

/-- S9 and S3/S5: the prepared claim, two challenges, and returned source
pairing agree with the precise model functionals/dual folds. S8 is kept
separately at the accumulator interface. Reader/R12/R13 identification chooses d. -/
structure PairingLaws (ops : AspisR1Stage2.Stage2Finish.FinishOps W) (decode : AspisR1Stage2.Stage2Finish.E → F)
    (v : verifier.View) (p : verifier.Prepared) (d : MatchingSupport.Data F) : Prop where
  round0 : RoundLaws ops decode v.round0 d.p0
  round1 : RoundLaws ops decode v.round1 d.p1
  claim : decode p.claim = JointFunctionalBinding.claimedValue d.Y d.c0 d.gamma d.kappa
  alpha0 : ∀ x, Array.index_usize p.alpha 0#usize = ok x → decode x = d.alpha0
  alpha1 : ∀ x, Array.index_usize p.alpha 1#usize = ok x → decode x = d.alpha1
  pair : ∀ weights alphas value,
    ops.newWeights p.variant p.semantic_alpha p.z = ok (.Ok weights) →
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice AspisR1Stage2.Stage2Finish.E)) p.alpha { «end» := 2#usize } = ok alphas →
    ops.pair weights alphas v.final_message p.kappa = ok (.Ok value) →
    decode value = RoundPairing.dot d.f
      (RoundPairing.dualFold (n := 64) d.alpha1
        (RoundPairing.dualFold (n := 256) d.alpha0
          (FunctionalWeights.weights d.F d.F0 d.kappa)))

/-- Both boundary equations and the final-value pairing are derived from
successful extracted control flow; no model pairing check is an input. -/
theorem finish_acceptedPairing (ops : AspisR1Stage2.Stage2Finish.FinishOps W) (decode : AspisR1Stage2.Stage2Finish.E → F)
    (compare : ComparisonLaw ops decode) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
    (d : MatchingSupport.Data F) (laws : PairingLaws ops decode v p d)
    (two : ops.folds p.variant = ok 2#usize)
    (h : AspisR1Stage2.Stage2Finish.verifier.finishRelationWithOps ops v p a obs = ok (.Ok ())) :
    MatchingSupport.AcceptedPairing d := by
  obtain ⟨alpha0,claim0,alpha1,claim1,weights,alphas,pair,actual,
    ha0,hr0,ha1,hr1,hw,has,hp,hpc,hd,hn,hdc⟩ := AspisR1Stage2.Stage2Finish.finish_success ops v p a obs two h
  obtain ⟨hb0,he0⟩ := round_refines ops decode compare v.round0 d.p0 laws.round0
    alpha0 p.claim claim0 0#usize hr0
  obtain ⟨hb1,he1⟩ := round_refines ops decode compare v.round1 d.p1 laws.round1
    alpha1 claim0 claim1 1#usize hr1
  rw [laws.claim] at hb0
  rw [laws.alpha0 alpha0 ha0] at he0
  rw [laws.alpha1 alpha1 ha1] at he1
  refine ⟨?_,?_,hb0⟩
  · exact he1.symm.trans ((compare pair claim1 hpc).symm.trans (laws.pair weights alphas pair hw has hp))
  · exact hb1.trans (congrArg (fun x => RoundPairing.quarter * x) he0)

/-- Supply exactly Checks.pairingChecks after the same-transcript matching read. -/
theorem finish_pairingChecks (ops : AspisR1Stage2.Stage2Finish.FinishOps W)
    (decode : AspisR1Stage2.Stage2Finish.E → AspisWideTower.WideExact)
    (compare : ComparisonLaw ops decode) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (d : MatchingSupport.Data AspisWideTower.WideExact)
    (read : LiteralMatchingData.read rs = some d)
    (laws : PairingLaws ops decode v p d) (two : ops.folds p.variant = ok 2#usize)
    (h : AspisR1Stage2.Stage2Finish.verifier.finishRelationWithOps ops v p a obs = ok (.Ok ())) :
    LiteralPairingChecks.checks rs := by
  exact (LiteralPairingChecks.acceptedPairing_iff_checks rs d read).mp
    (finish_acceptedPairing ops decode compare v p a obs d laws two h)

#print axioms round_refines
#print axioms finish_acceptedPairing
#print axioms finish_pairingChecks
end AspisR1.Stage2FinishPairing
end
