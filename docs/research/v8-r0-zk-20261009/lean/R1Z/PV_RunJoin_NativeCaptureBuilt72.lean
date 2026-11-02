import R1Z.PV_RunJoin_CaptureBuilt72
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeCaptureBuilt72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
abbrev Q := aspis_core.field.QM31

theorem complete {S F T : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (public1 : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (types base))
    (compiled : @aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (types base))
    (noised : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (maskOnly : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
    (d g padding : Array Q 1024#usize) (initial backend : prover.Backend)
    (hash : aspis_core.digest.LegacyHashFn) (variant : transport.Variant)
    (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (audit : prover.MaskedFixtureAudit) (store : T)
    (built : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (success : letI : ExternalTypes := types base
      letI : ExternalFuns := opsNative base heap box ops runtime world
      @host_semantic.build_with_material (types base) (opsNative base heap box ops runtime world)
      _ _ aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
      prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments
      public1 compiled noised maskOnly d g padding initial hash variant=ok (.Ok built,backend)) :
    letI : ExternalTypes := types base
    @PV_RunJoin_NativeAfterBuild55.run (types base) (opsNative base heap box ops runtime world) _ T
      PV_RunJoin_ActualProvenance60.capture public1 variant hash backend reserved context audit store (.Ok built)=
      ok (.Ok (⟨public1,variant,hash,backend,built,(reserved,context)⟩,
        {audit with h1_total_balanced:=true}),store) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  exact PV_RunJoin_CaptureBuilt72.complete (PV_RunJoin_NativeResidual62.baseTypes base) heap box
    (residual base ops runtime world) public1 compiled noised maskOnly d g padding initial backend
    hash variant reserved context audit store built success

#print axioms complete
end R1Z.PV_RunJoin_NativeCaptureBuilt72
