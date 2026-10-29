import R1Z.PV_RunJoin_MaterialAlphaProduced51
import R1Z.PV_RunJoin_BuildMaterialCircle51
import R1Z.PV_RunJoin_TwoPointFields51
import R1Z.PV_RunJoin_SemanticClaimPoint50
import R1Z.PV_RunJoin_SemanticMaterialInputs50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MaterialPointOrigins51
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
    ∃ (before middle : host_wire.SemanticTranscript aspis_core.digest.LegacyHashFn)
      (z0 z1 : aspis_core.circle.SecureCirclePoint) (f25 f26 : Slice U8),
      @host_wire.SemanticTranscript.challenge_reference_circle_point (types base) (selected base heap box ops) _ D
        before 25#u8 f25=ok (.Ok z0,middle) ∧
      @host_wire.SemanticTranscript.challenge_reference_circle_point (types base) (selected base heap box ops) _ D
        middle 26#u8 f26=ok (.Ok z1,built.transcript) ∧
      built.z=Array.make 2#usize [z0,z1] ∧
      PV_RunJoin_SemanticMaterialInputs50.x0 built=PV_RunJoin_SemanticScalar50.raw z0.x ∧
      PV_RunJoin_SemanticMaterialInputs50.y0 built=PV_RunJoin_SemanticScalar50.raw z0.y ∧
      PV_RunJoin_SemanticMaterialInputs50.x1 built=PV_RunJoin_SemanticScalar50.raw z1.x ∧
      PV_RunJoin_SemanticMaterialInputs50.y1 built=PV_RunJoin_SemanticScalar50.raw z1.y ∧
      PV_RunJoin_SemanticClaimPoint50.point built.z=
        ⟨ProverRwDictionaryTower.fromW (ProverCommitNativeOps47.embedded
          (ProverCommitNativeOps47.normalize (PV_RunJoin_SemanticScalar50.raw z1.x))),
         ProverRwDictionaryTower.fromW (ProverCommitNativeOps47.embedded
          (ProverCommitNativeOps47.normalize (PV_RunJoin_SemanticScalar50.raw z1.y)))⟩ := by
  have circles := PV_RunJoin_BuildMaterialCircle51.complete base heap box ops D commitInst public1 compiled
    noised maskOnly d g padding commitments hash variant
  rw [success] at circles
  obtain ⟨before,middle,z0,z1,f25,f26,h25,h26,hz⟩ := circles
  obtain ⟨hx0,hy0,hx1,hy1⟩ := PV_RunJoin_TwoPointFields51.raw built z0 z1 hz
  exact ⟨before,middle,z0,z1,f25,f26,h25,h26,hz,hx0,hy0,hx1,hy1,
    PV_RunJoin_TwoPointFields51.claim built z0 z1 hz⟩
#print axioms complete
end R1Z.PV_RunJoin_MaterialPointOrigins51
