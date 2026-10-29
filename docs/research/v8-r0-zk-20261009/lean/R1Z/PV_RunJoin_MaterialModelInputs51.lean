import R1Z.PV_RunJoin_MaterialAlphaProduced51
import R1Z.PV_RunJoin_SemanticMaterial50
import R1Z.PV_RunJoin_SemanticClaimPoint50
import R1Z.PV_RunJoin_SemanticMaterialInputs50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MaterialModelInputs51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 PV_RunJoin_ResultPost41
open PV_RunJoin_PointPrefix51 (Prefix)
abbrev Q := ProverRwFull.aspis_core.field.QM31

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {T : Type} (D : aspis_core.digest.Digest32 aspis_core.digest.LegacyHashFn) (commitInst : host_semantic.Commitments T)
    (public1 : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (types base))
    (compiled : @aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (types base))
    (noised : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (maskOnly : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
    (d g padding : Array Q 1024#usize) (commitments nextCommitments : T) (hash : aspis_core.digest.LegacyHashFn) (variant : transport.Variant)
    (built : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (success : @host_semantic.build_with_material (types base) (selected base heap box ops)
      aspis_core.digest.LegacyHashFn T D commitInst public1 compiled noised maskOnly d g padding commitments hash variant=ok (.Ok built,nextCommitments)) :
    (∀ i,i<10 → ProverCommitSubfieldOps47.Canonical (PV_RunJoin_SemanticMaterialInputs50.alpha built i)) ∧
    (ProverCommitSubfieldOps47.Canonical (PV_RunJoin_SemanticClaimPoint50.x built.z) ∧
      ProverCommitSubfieldOps47.Canonical (PV_RunJoin_SemanticClaimPoint50.y built.z)) ∧
    ∃ kw : PV_B2_F_ConstructorCarrier.Weight,
      (PV_B2_F_ConstructorCarrier.toWeight kw).variant=.S2 ∧
      (selected base heap box ops).op252 .S2 built.alpha built.z=(do
        let _ ← box .S2 built.alpha built.z
        ok (.Ok (PV_B2_F_ConstructorCarrier.toWeight kw))) ∧
      (∀ x : PV_RunJoin_MaterialVec49.S,
        (selected base heap box ops).op251 (PV_B2_F_ConstructorCarrier.toWeight kw) (ProverRwDictionaryTower.fromW x)=
          PV_RunJoin_MaterialRun49.outcome (heap (PV_B2_F_ConstructorCarrier.toWeight kw) (ProverRwDictionaryTower.fromW x))
            (ProverCommitWeightsMaterial53.run
              (ProverCommitQArray48.array 10#usize (PV_RunJoin_SemanticMaterialInputs50.alpha built))
              (ProverCommitNativeQ48.source (PV_RunJoin_SemanticMaterialInputs50.x0 built))
              (ProverCommitNativeQ48.source (PV_RunJoin_SemanticMaterialInputs50.y0 built))
              (ProverCommitNativeQ48.source (PV_RunJoin_SemanticMaterialInputs50.x1 built))
              (ProverCommitNativeQ48.source (PV_RunJoin_SemanticMaterialInputs50.y1 built)) x)) := by
  exact ⟨PV_RunJoin_MaterialAlphaProduced51.complete base heap box ops D commitInst public1 compiled noised maskOnly
    d g padding commitments nextCommitments hash variant built success,
    PV_RunJoin_SemanticClaimPoint50.canonical built.z,
    PV_RunJoin_SemanticMaterial50.complete base heap box ops built⟩
#print axioms complete
end R1Z.PV_RunJoin_MaterialModelInputs51
