import R1Z.PV_OptB_Cardinality
import R1Z.PV_Src_Fixture_FixtureFibres
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_AdmittedFamily
open R0P AspisR1.SpendRelation R1Z.BuilderSpendRelation PV_OptB_WitnessFamily
open R1J.SpendWitnessMap
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

abbrev M := R1J.SpendWitnessMap.F

def admitted (pub : Public M) (w : Wspend) (valid : RspendPlus pub w) (t : Fin 16 → M) :
    BuilderCanonical.Instance (K := K) :=
  ⟨(publicInput pub w t,witness w t),
    PV_Src_Fixture_FixtureFibres.lift_spendPlus _ _ (rspendPlus pub w valid t)⟩

theorem exists_distinct_admitted (pub : Public M) (w : Wspend) (valid : RspendPlus pub w) :
    ∃ a b : BuilderCanonical.Instance (K := K),
      (BuilderSource.prover (K := K)).public a = (BuilderSource.prover (K := K)).public b ∧ a ≠ b := by
  obtain ⟨t,u,same,different,_,_⟩ := PV_OptB_Cardinality.same_public_distinct_witnesses pub w valid
  refine ⟨admitted pub w valid t,admitted pub w valid u,?_,?_⟩
  · exact congrArg (mapPub (K := K)) same
  · intro equal
    exact different (congrArg (fun a : BuilderCanonical.Instance (K := K) => a.val.2) equal)

/-- Concrete admitted base from the existing symbolic withdrawal fixture.
This establishes nonvacuity of the honest-witness family, not native trace
or byte identity for a colliding pair. -/
theorem exists_distinct_fixture_admitted :
    ∃ a b : BuilderCanonical.Instance (K := K),
      (BuilderSource.prover (K := K)).public a = (BuilderSource.prover (K := K)).public b ∧ a ≠ b :=
  exists_distinct_admitted (PV_Src_Fixture_FixtureRecords.fixturePublic true)
    (PV_Src_Fixture_FixtureRecords.witness true) PV_Src_Fixture_FixtureRecords.withdrawal_spendPlus

#print axioms admitted
#print axioms exists_distinct_admitted
#print axioms exists_distinct_fixture_admitted
end R1Z.PV_OptB_AdmittedFamily
