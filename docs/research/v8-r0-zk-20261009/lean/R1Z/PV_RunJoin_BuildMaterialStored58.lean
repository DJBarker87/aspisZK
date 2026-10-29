import R1Z.PV_RunJoin_BuildMaterialBackendLength58
import R1Z.PV_RunJoin_BuildMaterialAlpha51
import R1Z.PV_RunJoin_BuildMaterialCircle51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BuildMaterialStored58
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (public1 : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (types base))
    (compiled : @aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (types base))
    (noised : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (maskOnly : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
    (d g padding : Array aspis_core.field.QM31 1024#usize)
    (start backend : prover.Backend) (hash : H) (variant : transport.Variant)
    (built : host_semantic.BuiltSemantics H) (length : start.messages.length=29)
    (success : @host_semantic.build_with_material (types base) (selected base heap box ops)
      H prover.Backend D
      (@prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments (types base) (selected base heap box ops))
      public1 compiled noised maskOnly d g padding start hash variant=ok (.Ok built,backend)) :
    PV_RunJoin_PointPrefix51.Prefix 10 built.alpha ∧
    @PV_RunJoin_CircleProduced51.Produced (types base) (selected base heap box ops) H D built ∧
    backend.messages.length=29 := by
  have ha := PV_RunJoin_BuildMaterialAlpha51.complete base heap box ops D
    (@prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments (types base) (selected base heap box ops))
    public1 compiled noised maskOnly d g padding start hash variant
  have hz := PV_RunJoin_BuildMaterialCircle51.complete base heap box ops D
    (@prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments (types base) (selected base heap box ops))
    public1 compiled noised maskOnly d g padding start hash variant
  have hl := PV_RunJoin_BuildMaterialBackendLength58.complete base heap box ops D
    public1 compiled noised maskOnly d g padding start hash variant length
  rw [success] at ha hz hl
  exact ⟨ha,hz,hl⟩

#print axioms complete
end R1Z.PV_RunJoin_BuildMaterialStored58
