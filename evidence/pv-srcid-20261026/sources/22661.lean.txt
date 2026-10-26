import R1Z.PV_Src_ForestCanonical
import R1Z.PV_Src_Fixture_CanonicalFixtures

/-! Concrete inhabitance for both canonical fixture fibres, including an
actual successful extracted bank/column run. Re-encoding these field values
does not identify release bytes or supply a native entry-point execution. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_Fixtures
open Aeneas Aeneas.Std Result R0P R1J.SpendWitnessMap
open PV_Src_Fixture_CanonicalFixtures
abbrev Scalar := PrivacyR1AcctBasis.K
local instance : CharP Scalar 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) Scalar).injective
    AspisCircleGroupOrder.P

def fixture (isWithdrawal : Bool) : PV_Src_ForestCanonical.Instance (K := Scalar) where
  canonical := if isWithdrawal then withdrawal else transfer
  indexBound := by cases isWithdrawal <;> change 0 < 2^64 <;> decide
  pool := Array.repeat 32#usize 0#u8
  domain := Array.repeat 32#usize 0#u8
  destination := Array.repeat 32#usize 0#u8

theorem inhabited : Nonempty (PV_Src_ForestCanonical.Instance (K := Scalar)) := ⟨fixture false⟩

theorem fixture_run (b : Bool) :
    ∃ out, PV_Src_ForestTrace.run
      (PV_Src_ForestCanonical.inputs (fixture b)).witnessRecord
      (PV_Src_ForestCanonical.inputs (fixture b)).publicRecord = ok out := by
  obtain ⟨out,ho,_,_⟩ := PV_Src_ForestTrace.run_exact
    (PV_Src_ForestCanonical.inputs (fixture b)).witnessRecord
    (PV_Src_ForestCanonical.inputs (fixture b)).publicRecord
  exact ⟨out,ho⟩

theorem transfer_public :
    (PV_Src_ForestIdentification.prover PV_Src_ForestCanonical.inputs PV_Src_Transport.transport).public
      (fixture false) = mapPub (PV_Src_Fixture_FixtureRecords.fixturePublic false) :=
  (PV_Src_ForestCanonical.public_eq (fixture false)).trans
    PV_Src_Fixture_CanonicalFixtures.transfer_public

theorem withdrawal_public :
    (PV_Src_ForestIdentification.prover PV_Src_ForestCanonical.inputs PV_Src_Transport.transport).public
      (fixture true) = mapPub (PV_Src_Fixture_FixtureRecords.fixturePublic true) :=
  (PV_Src_ForestCanonical.public_eq (fixture true)).trans
    PV_Src_Fixture_CanonicalFixtures.withdrawal_public

theorem fixture_build (b : Bool) :
    (PV_Src_ForestIdentification.prover PV_Src_ForestCanonical.inputs PV_Src_Transport.transport).build
      (fixture b) = BuilderSource.prover.build (fixture b).canonical :=
  PV_Src_ForestCanonical.build_eq _

/-- Both model fibres are inhabited by successful actual extracted-stage
computations. The same field-public statements and arbitrary handles are used. -/
theorem fibres {CommitHandle : Type} (ht hw : CommitHandle) :
    let xt : R0Z.ZkStatement.Statement Scalar CommitHandle :=
      (mapPub (PV_Src_Fixture_FixtureRecords.fixturePublic false),ht)
    let xw : R0Z.ZkStatement.Statement Scalar CommitHandle :=
      (mapPub (PV_Src_Fixture_FixtureRecords.fixturePublic true),hw)
    ∃ wt ww : (PV_Src_ForestIdentification.prover (K := Scalar) (PV_Src_ForestCanonical.inputs (K := Scalar))
      PV_Src_Transport.transport).Instance,
      (PV_Src_ForestIdentification.prover PV_Src_ForestCanonical.inputs PV_Src_Transport.transport).public wt = xt.1 ∧
      (PV_Src_ForestIdentification.prover PV_Src_ForestCanonical.inputs PV_Src_Transport.transport).public ww = xw.1 :=
  ⟨fixture false,fixture true,transfer_public,withdrawal_public⟩

#print axioms fixture
#print axioms inhabited
#print axioms fixture_run
#print axioms transfer_public
#print axioms withdrawal_public
#print axioms fixture_build
#print axioms fibres
end R1Z.PV_Src_Fixtures
