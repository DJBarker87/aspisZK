import R1Z.PV_RunJoin_BuildCircleProduced51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BuildMaterialCircle51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 PV_RunJoin_ResultPost41
open PV_RunJoin_PointPrefix51 (Prefix)
abbrev Q := ProverRwFull.aspis_core.field.QM31

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H T : Type} (D : aspis_core.digest.Digest32 H) (commitInst : host_semantic.Commitments T)
    (public1 : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (types base))
    (compiled : @aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (types base))
    (noised : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (maskOnly : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
    (d g padding : Array Q 1024#usize) (commitments : T) (hash : H) (variant : transport.Variant) :
    Post (fun pair => match pair.1 with | .Err _ => True | .Ok built => @PV_RunJoin_CircleProduced51.Produced (types base) (selected base heap box ops) H D built)
      (@host_semantic.build_with_material (types base) (selected base heap box ops)
        H T D commitInst public1 compiled noised maskOnly d g padding commitments hash variant) := by
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
        exact PV_RunJoin_BuildCircleProduced51.complete base heap box ops D _ commitInst
          public1 columns d g padding (compiled,public1) commitments hash variant
#print axioms complete
end R1Z.PV_RunJoin_BuildMaterialCircle51
