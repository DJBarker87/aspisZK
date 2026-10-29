import R1Z.PV_RunJoin_MaterialAlphaProduced51
import R1Z.PV_RunJoin_NormalizeFixed51
import R1Z.PV_RunJoin_SemanticMaterialInputs50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MaterialAlphaFixed51
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
    (d g padding : Array Q 1024#usize) (commitments nextCommitments : T) (hash : H) (variant : transport.Variant)
    (built : host_semantic.BuiltSemantics H)
    (success : @host_semantic.build_with_material (types base) (selected base heap box ops)
      H T D commitInst public1 compiled noised maskOnly d g padding commitments hash variant=ok (.Ok built,nextCommitments)) :
    ∀ i,i<10 → ProverCommitNativeOps47.normalize (PV_RunJoin_SemanticArray50.raw 10#usize built.alpha i)=
      PV_RunJoin_SemanticArray50.raw 10#usize built.alpha i := by
  have canonical := PV_RunJoin_MaterialAlphaProduced51.complete base heap box ops D commitInst public1 compiled
    noised maskOnly d g padding commitments nextCommitments hash variant built success
  intro i hi
  exact PV_RunJoin_NormalizeFixed51.fixed _ (canonical i hi)
#print axioms complete
end R1Z.PV_RunJoin_MaterialAlphaFixed51
