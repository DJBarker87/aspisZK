import R1Z.PV_RunJoin_ConsumerBoundary25
import R1Z.PV_RunJoin_UniversalCompilerFrame22
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_HonestIdentification26
open Aeneas Aeneas.Std Result PV_Src_NativeInput
local notation "E" => PV_RunJoin_ShippedExternal.E_shipped
local notation "R" => PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- The honest prover chooses among compiler-produced, admitted inputs with
all representation guards. The generic identification contract is unchanged. -/
abbrev Honest := {i : Input // PV_RunJoin_ConsumerBoundary25.HonestInput (K := K) i}
def inputs (i : Honest (K := K)) : Input := i.val

theorem admitted (i : Honest (K := K)) :
    PV_RunJoin_UniversalBuild22.Admission (K := K) (inputs i) := i.property.1
#print axioms admitted

theorem success (i : Honest (K := K)) :
    @run E R (inputs i) = ok (.Ok (inputs i).compiled) := i.property.2.1
#print axioms success

def source_honest := PV_Src_NativeIdentification.prover (K := K)
  (inputs (K := K)) PV_Src_Transport.transport

def target : Honest (K := K) → BuilderCanonical.Instance (K := K) :=
  PV_RunJoin_UniversalBuild22.toInstance inputs admitted

/-- V152, universally on the honest family. -/
theorem public_eq (i : Honest (K := K)) :
    source_honest.public i = BuilderSource.prover.public (target i) :=
  PV_RunJoin_UniversalBuild22.public_eq inputs _ admitted i
#print axioms public_eq

/-- V153, universally on the honest family, by symbolic returned-bank and
merged/canonical trace laws; no complete run is reduced. -/
theorem build_eq (i : Honest (K := K)) :
    source_honest.build i = BuilderSource.prover.build (target i) :=
  PV_RunJoin_UniversalBuild22.build_eq inputs _ admitted success
    (fun i => i.property.2.2.1) (fun i => i.property.2.2.2) i
#print axioms build_eq

/-- V154 is the unchanged D18 row equivalence. -/
theorem transport_eq : (source_honest (K := K)).transport = BuilderSource.π :=
  PV_RunJoin_UniversalBuild22.transport_eq inputs
#print axioms transport_eq

/-- Exactly the original three fields, instantiated at the honest family. -/
theorem identification : BuilderSource.SourceIdentification
    (source_honest (K := K)) target :=
  ⟨public_eq, build_eq, transport_eq⟩
#print axioms identification

/-- Full compiler-associated transition at every honest input. -/
theorem transition (i : Honest (K := K)) :
    PV_Src_NativeInput.transition (inputs i).compiled.public_statement =
      { live_snapshot := {
          pool := (inputs i).snapshot.pool,
          deployment_domain := (inputs i).snapshot.deployment_domain,
          sequence := (inputs i).snapshot.sequence,
          next_pair_index := (inputs i).snapshot.next_pair_index,
          current_root := (inputs i).snapshot.current_root,
          frontier := (inputs i).snapshot.frontier },
        candidate_afterstate := {
          next_pair_index := (inputs i).compiled.trace.afterstate.next_pair_index,
          next_root := (inputs i).compiled.trace.afterstate.next_root,
          next_frontier := (inputs i).compiled.trace.afterstate.next_frontier } } :=
  @PV_RunJoin_UniversalTransition22.transition E R (inputs i) (success i)
#print axioms transition

/-- The full successful payload fixes directions, value bits and variant;
this fact is not inferred from identification alone. -/
theorem compiler_frame (i : Honest (K := K)) :
    (inputs i).compiled.trace.private_directions =
      BuilderRecordsPath.bits (PV_Src_NativeDirections.reference (inputs i).witness) ∧
    (inputs i).compiled.trace.value_bits = Array.make 3#usize
      [PV_RunJoin_ValueBits20.bits (inputs i).witness.pair.value,
       PV_RunJoin_ValueBits20.bits (outputValue (inputs i).request),
       PV_RunJoin_ValueBits20.bits (inputs i).change.value] ∧
    (inputs i).compiled.trace.variant = (match (inputs i).request with
      | .transfer _ _ => BuilderForestAdmissionPort.pool_v1.pair_trace.PoolV1PairTraceVariantV1.PrivateTransfer
      | .withdrawal _ => .Withdrawal) :=
  @PV_RunJoin_UniversalCompilerFrame22.native E R (inputs i) (success i)
#print axioms compiler_frame
end R1Z.PV_RunJoin_HonestIdentification26
