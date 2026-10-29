import R1Z.PV_RunJoin_ActualProvenance60
import R1Z.PV_RunJoin_ResultPost41
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BuildOrigin60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
variable [ExternalTypes] [ExternalFuns]

/-- An actual upstream builder equation and its initialized backend length.
This certificate says nothing about hinput, canonicality or publication bytes. -/
def Origin (p : Phase) : Prop :=
  p.variant=.S2 ∧ ∃
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (noised : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (maskOnly : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
    (d g padding : Array aspis_core.field.QM31 1024#usize)
    (initial : prover.Backend),
    initial.messages.length=29 ∧
    host_semantic.build_with_material
      aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
      prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments
      p.public1 compiled noised maskOnly d g padding initial p.hash .S2=ok (.Ok p.sem,p.backend)

#print axioms Origin
end R1Z.PV_RunJoin_BuildOrigin60
