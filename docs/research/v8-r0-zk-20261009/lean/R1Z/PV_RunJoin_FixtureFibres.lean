import R1Z.PV_RunJoin_FixtureRecords
import R1Z.PV_RunJoin_SpendRelationMap
import R1Z.BuilderSource

/-! Explicit canonical mathematical fixture instances. Association with
released Rust public records/bytes remains named; no arbitrary x is silently
identified with these records. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureFibres
open R0P AspisR1 AspisR1.SpendRelation
open R1J.SpendWitnessMap BuilderCanonical BuilderSpendRelation
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem lift_spendPlus (pub : Public R1J.SpendWitnessMap.F) (w : Wspend)
    (valid : RspendPlus pub w) : RspendPlus (mapPub (K := K) pub) (liftWitness w) := by
  refine ⟨?_,?_⟩
  · change Rspend (PV_RunJoin_SpendDataMap.mapPublic ι pub) (PV_RunJoin_SpendDataMap.witness ι w)
    exact (PV_RunJoin_SpendRelationMap.rspend_map_iff ι pub w).mpr valid.1
  · intro variant zero
    apply valid.2 variant
    apply (ι : R1J.SpendWitnessMap.F →+* K).injective
    change ι (pub.change 7) = ι 0
    simpa only [R1J.SpendWitnessMap.mapPub,map_zero] using zero

def withdrawal : BuilderCanonical.Instance (K := K) :=
  ⟨(PV_RunJoin_FixtureRecords.fixturePublic true,PV_RunJoin_FixtureRecords.witness true),
    lift_spendPlus _ _ PV_RunJoin_FixtureRecords.withdrawal_spendPlus⟩

def transfer (sentinel : (PV_RunJoin_FixtureRecords.fixturePublic false).change 7 ≠ 0) :
    BuilderCanonical.Instance (K := K) :=
  ⟨(PV_RunJoin_FixtureRecords.fixturePublic false,PV_RunJoin_FixtureRecords.witness false),
    lift_spendPlus _ _ (PV_RunJoin_FixtureRecords.transfer_spendPlus sentinel)⟩

theorem withdrawal_public :
    (BuilderSource.prover (K := K)).public withdrawal =
      mapPub (PV_RunJoin_FixtureRecords.fixturePublic true) := rfl

theorem transfer_public (sentinel : (PV_RunJoin_FixtureRecords.fixturePublic false).change 7 ≠ 0) :
    (BuilderSource.prover (K := K)).public (transfer sentinel) =
      mapPub (PV_RunJoin_FixtureRecords.fixturePublic false) := rfl

/-- Explicit remaining fixture laws. These are not discharged by the
canonical constructors. The public equations refer to the actual chosen
statements; the transfer sentinel is the D50 mathematical guard. -/
structure FixturePremises {CommitHandle : Type}
    (transferX withdrawalX : R0Z.ZkStatement.Statement K CommitHandle) : Prop where
  transfer_public_V047 : transferX.1 = mapPub (PV_RunJoin_FixtureRecords.fixturePublic false)
  withdrawal_public_V047 : withdrawalX.1 = mapPub (PV_RunJoin_FixtureRecords.fixturePublic true)
  transfer_sentinel_V047 : (PV_RunJoin_FixtureRecords.fixturePublic false).change 7 ≠ 0

theorem release_fibres {CommitHandle : Type}
    (transferX withdrawalX : R0Z.ZkStatement.Statement K CommitHandle)
    (premises : FixturePremises transferX withdrawalX) :
    ∃ wt ww : (BuilderSource.prover (K := K)).Instance,
      (BuilderSource.prover (K := K)).public wt = transferX.1 ∧
      (BuilderSource.prover (K := K)).public ww = withdrawalX.1 := by
  exact ⟨transfer premises.transfer_sentinel_V047,withdrawal,
    (transfer_public _).trans premises.transfer_public_V047.symm,
    withdrawal_public.trans premises.withdrawal_public_V047.symm⟩

#print axioms lift_spendPlus
#print axioms withdrawal
#print axioms transfer
#print axioms withdrawal_public
#print axioms transfer_public
#print axioms release_fibres
end R1Z.PV_RunJoin_FixtureFibres
