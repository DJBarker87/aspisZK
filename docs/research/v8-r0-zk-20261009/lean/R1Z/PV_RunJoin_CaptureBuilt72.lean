import R1Z.PV_RunJoin_CaptureTail72
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CaptureBuilt72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
abbrev Q := aspis_core.field.QM31

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {T : Type}
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
    (success : @host_semantic.build_with_material (types base) (selected base heap box ops)
      _ _ aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
      prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments
      public1 compiled noised maskOnly d g padding initial hash variant=ok (.Ok built,backend)) :
    letI : ExternalTypes := types base
    @PV_RunJoin_NativeAfterBuild55.run (types base) (selected base heap box ops) _ T
      PV_RunJoin_ActualProvenance60.capture public1 variant hash backend reserved context audit store (.Ok built)=
      ok (.Ok (⟨public1,variant,hash,backend,built,(reserved,context)⟩,
        {audit with h1_total_balanced:=true}),store) := by
  letI : ExternalTypes := types base
  have balanced := PV_RunJoin_BuiltHelper72.complete base heap box ops
    aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments public1 compiled noised
    maskOnly d g padding initial backend hash variant built success
  exact PV_RunJoin_CaptureTail72.complete base heap box ops public1 hash variant backend
    reserved context audit store built balanced

#print axioms complete
end R1Z.PV_RunJoin_CaptureBuilt72
