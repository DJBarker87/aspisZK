import R1Z.PV_RunJoin_BuildBackendLength58
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BuildMaterialBackendLength58
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 PV_RunJoin_ResultPost41
abbrev Q := ProverRwFull.aspis_core.field.QM31

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (public1 : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (types base))
    (compiled : @aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (types base))
    (noised : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (maskOnly : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
    (d g padding : Array Q 1024#usize) (commitments : prover.Backend) (hash : H) (variant : transport.Variant)
    (hlen : commitments.messages.length=29) :
    Post (fun pair => match pair.1 with | .Err _ => True | .Ok _ => pair.2.messages.length=29)
      (@host_semantic.build_with_material (types base) (selected base heap box ops)
        H prover.Backend D
          (@prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments (types base) (selected base heap box ops)) public1 compiled noised maskOnly d g padding commitments hash variant) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  unfold host_semantic.build_with_material
  simp only [lift,bind_tc_ok]
  split
  · trivial
  · split
    · trivial
    · apply PV_RunJoin_ResultPost41.bind
      intro transition
      apply PV_RunJoin_ResultPost41.bind
      intro different
      cases different with
      | true => trivial
      | false =>
        simp only [Bool.false_eq_true,if_false,lift,bind_tc_ok]
        apply PV_RunJoin_ResultPost41.bind
        intro columns
        exact PV_RunJoin_BuildBackendLength58.complete base heap box ops D _
          public1 columns d g padding (compiled,public1) commitments hash variant hlen
#print axioms complete
end R1Z.PV_RunJoin_BuildMaterialBackendLength58
