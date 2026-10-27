import R1Z.PV_RunJoin_PremiseTruth24
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ConsumerBoundary25
open Aeneas Aeneas.Std Result PV_Src_NativeInput
local notation "E" => PV_RunJoin_ShippedExternal.E_shipped
local notation "R" => PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Diagnostic predicate for the proposed carrier, not a replacement handoff.
Every explicit guard of UniversalBuild22 is retained. -/
def HonestInput (i : Input) : Prop :=
  PV_RunJoin_UniversalBuild22.Admission (K := K) i ∧
  @run E R i = ok (.Ok i.compiled) ∧
  PV_Src_RecordReference.Checked i ∧
  ∀ l : Fin 20, R0Z.WriterRefine.Canon8 i.snapshot.frontier.val[l.val]!

abbrev bad := PV_RunJoin_AdmittedReturnCounterexample23.counterexample

def inputs (_ : Unit) : Input := bad
abbrev source := PV_Src_NativeIdentification.prover (K := K) inputs PV_Src_Transport.transport

def target : Unit → BuilderCanonical.Instance (K := K) :=
  PV_RunJoin_UniversalBuild22.toInstance inputs
    (fun _ => PV_RunJoin_AdmittedReturnCounterexample23.admitted)

/-- The original, unrestricted three-field certificate really is inhabited
on this singleton native family, although the cached payload is dishonest. -/
theorem identification : BuilderSource.SourceIdentification (source (K := K)) target where
  public_eq := fun _ => PV_RunJoin_PremiseTruth24.variant_public_eq
  build_eq := fun _ => PV_RunJoin_PremiseTruth24.variant_build_eq
  transport_eq := PV_RunJoin_PremiseTruth24.raw_transport_eq (K := K)
#print axioms identification

theorem not_honest : ¬ HonestInput (K := K) (inputs ()) := by
  intro h
  exact PV_RunJoin_AdmittedReturnCounterexample23.not_cached_return h.2.1
#print axioms not_honest

/-- The all-consumer honesty assertion is false even with a satisfiable
SourceIdentification, semantic admission and all other symbolic guards. -/
theorem identification_does_not_imply_honesty :
    ¬ (BuilderSource.SourceIdentification (source (K := K)) target →
      ∀ w : Unit, HonestInput (K := K) (inputs w)) := by
  intro h
  exact not_honest (h identification ())
#print axioms identification_does_not_imply_honesty

/-- Both original successful fixtures satisfy the full proposed guards.
This does not install a new carrier or change the endpoint. -/
theorem transfer_honest : HonestInput (K := K) PV_RunJoin_AdmittedCarrier23.transfer :=
  ⟨PV_RunJoin_AdmittedCarrier23.transfer_admitted,
   PV_RunJoin_AdmittedCarrier23.transfer_return,
   PV_RunJoin_AdmittedCarrier23.transfer_checked,
   PV_RunJoin_AdmittedCarrier23.transfer_frontier⟩
#print axioms transfer_honest

theorem withdrawal_honest : HonestInput (K := K) PV_RunJoin_AdmittedCarrier23.withdrawal := by
  refine ⟨PV_RunJoin_AdmittedCarrier23.withdrawal_admitted,
    PV_RunJoin_AdmittedCarrier23.withdrawal_return, ?_, ?_⟩
  · exact ⟨PV_RunJoin_FixtureAdmission.withdrawal_values,PV_RunJoin_FixtureAdmission.first,
      PV_RunJoin_FixtureAdmission.second,PV_RunJoin_FixtureAdmission.membership,
      PV_RunJoin_FixtureAdmission.superRoot⟩
  · exact PV_RunJoin_AdmittedCarrier23.transfer_frontier
#print axioms withdrawal_honest
end R1Z.PV_RunJoin_ConsumerBoundary25
