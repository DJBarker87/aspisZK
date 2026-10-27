import R1Z.PV_OptB_DifferentNoPole
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_AdmittedTrace
open R0P AspisR1.SpendRelation R1Z.BuilderSpendRelation R1J.SpendWitnessMap
open PV_OptB_PathPoles
open PV_OptB_AdmittedFamily (admitted)
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem build_admitted (pub : Public M) (w : Wspend) (valid : RspendPlus pub w) (t : Fin 16 → M) :
    (BuilderSource.prover (K := K)).build (admitted pub w valid t) = trace pub w t := by
  change BuilderRefinement.mergedTrace
    (BuilderCanonical.rustWitness (PV_OptB_WitnessFamily.witness w t))
    (BuilderCanonical.rustPublic (PV_OptB_WitnessFamily.publicInput pub w t)) = _
  exact BuilderCanonical.canonical_trace _ _

#print axioms build_admitted
end R1Z.PV_OptB_AdmittedTrace
