import R1Z.PV_RunJoin_AdmissionBoundary23
import R1Z.PV_RunJoin_AdmittedReturnCounterexample23
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PremiseTruth24
open PV_Src_NativeInput R1J.SpendWitnessMap
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

abbrev raw := PV_Src_NativeIdentification.prover (K := K) (fun i : Input => i)
  PV_Src_Transport.transport

/-- The actual public computation is correct even on the rejected raw input.
This does not manufacture an inhabitant of the canonical relation. -/
theorem bad_public_projection :
    (raw (K := K)).public PV_RunJoin_AdmissionBoundary23.bad =
      mapPub (PV_Src_Public.canonicalPublic
        (publicInput PV_RunJoin_AdmissionBoundary23.bad)) :=
  PV_RunJoin_UniversalPublic22.projection _ _ _
#print axioms bad_public_projection

/-- No record-preserving canonical map can satisfy V152 at this raw input.
The public equation alone is not the semantic admission equation. -/
theorem bad_public_eq_false_of_witness
    (f : Input → BuilderCanonical.Instance (K := K))
    (hw : (f PV_RunJoin_AdmissionBoundary23.bad).val.2 =
      BuilderRecordCanonical.witness (PV_Src_Forest_PrimitiveArguments.wordWitness
        (PV_RunJoin_UniversalBuild22.records PV_RunJoin_AdmissionBoundary23.bad).w)) :
    (raw (K := K)).public PV_RunJoin_AdmissionBoundary23.bad ≠
      BuilderSource.prover.public (f PV_RunJoin_AdmissionBoundary23.bad) := by
  intro hp
  have h := (f PV_RunJoin_AdmissionBoundary23.bad).property
  change BuilderSpendRelation.RspendPlus
    (BuilderSource.prover.public (f PV_RunJoin_AdmissionBoundary23.bad))
    (BuilderCanonical.liftWitness (f PV_RunJoin_AdmissionBoundary23.bad).val.2) at h
  rw [← hp,bad_public_projection,hw] at h
  exact PV_RunJoin_AdmissionBoundary23.bad_not_admitted h
#print axioms bad_public_eq_false_of_witness

/-- Changing only trace.variant changes neither the raw columns nor the
public projection nor the compiler arguments. -/
theorem variant_build_preserved (i : Input) :
    (raw (K := K)).build (PV_RunJoin_PayloadAssociation22.altered i) =
      (raw (K := K)).build i := rfl
#print axioms variant_build_preserved

theorem variant_public_preserved (i : Input) :
    (raw (K := K)).public (PV_RunJoin_PayloadAssociation22.altered i) =
      (raw (K := K)).public i := rfl
#print axioms variant_public_preserved

/-- V153 is TRUE on the original admitted variant-only counterexample,
for the precise record/public canonical map used by UniversalBuild22. -/
theorem variant_build_eq :
    (raw (K := K)).build PV_RunJoin_AdmittedReturnCounterexample23.counterexample =
      BuilderSource.prover.build
        (PV_RunJoin_UniversalBuild22.toInstance
          (fun _ : Unit => PV_RunJoin_AdmittedReturnCounterexample23.counterexample)
          (fun _ => PV_RunJoin_AdmittedReturnCounterexample23.admitted) ()) := by
  exact PV_RunJoin_UniversalBuild22.build_eq
    (fun _ : Unit => PV_RunJoin_AdmittedCarrier23.transfer) PV_Src_Transport.transport
    (fun _ => PV_RunJoin_AdmittedCarrier23.transfer_admitted)
    (fun _ => PV_RunJoin_AdmittedCarrier23.transfer_return)
    (fun _ => PV_RunJoin_AdmittedCarrier23.transfer_checked)
    (fun _ => PV_RunJoin_AdmittedCarrier23.transfer_frontier) ()
#print axioms variant_build_eq

theorem variant_public_eq :
    (raw (K := K)).public PV_RunJoin_AdmittedReturnCounterexample23.counterexample =
      BuilderSource.prover.public
        (PV_RunJoin_UniversalBuild22.toInstance
          (fun _ : Unit => PV_RunJoin_AdmittedReturnCounterexample23.counterexample)
          (fun _ => PV_RunJoin_AdmittedReturnCounterexample23.admitted) ()) :=
  PV_RunJoin_UniversalBuild22.public_eq _ _ _ ()
#print axioms variant_public_eq

theorem raw_transport_eq : (raw (K := K)).transport = BuilderSource.π :=
  PV_RunJoin_UniversalBuild22.transport_eq _
#print axioms raw_transport_eq

#print BuilderSource.SourceIdentification
#print PV_Src_NativeIdentification.prover
#print BuilderCanonical.Instance
#print BuilderCanonical.prover
#print BuilderSource.prover
#print PV_RunJoin_UniversalBuild22.toInstance
end R1Z.PV_RunJoin_PremiseTruth24
