import R1Z.PV_RunJoin_MaterialPointOrigins51
import R1Z.PV_RunJoin_MaterialAlphaProduced51
import R1Z.PV_RunJoin_BuildMaterialCircle51
import R1Z.PV_RunJoin_TwoPointFields51
import R1Z.PV_RunJoin_SemanticClaimPoint50
import R1Z.PV_RunJoin_PrepareClaimInputs51
import R1Z.PV_RunJoin_SemanticMaterialInputs50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareOrigins51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 PV_RunJoin_ResultPost41
open PV_RunJoin_PointPrefix51 (Prefix)
abbrev Q := ProverRwFull.aspis_core.field.QM31

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {T : Type} (commitInst : host_semantic.Commitments T)
    (public1 : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (types base))
    (compiled : @aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (types base))
    (noised : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (maskOnly : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
    (d g padding : Array Q 1024#usize) (commitments nextCommitments : T) (hash : aspis_core.digest.LegacyHashFn) 
    (built : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (success : @host_semantic.build_with_material (types base) (selected base heap box ops)
      aspis_core.digest.LegacyHashFn T (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops)) commitInst public1 compiled noised maskOnly d g padding commitments hash .S2=ok (.Ok built,nextCommitments))
    (backend : prover.Backend) (out : prover.PreparedOpening)
    (prepare : @prover.prepare_opening (types base) (selected base heap box ops) .S2 hash backend built=ok (.Ok out)) :
    (∀ i,i<10 → ProverCommitSubfieldOps47.Canonical (PV_RunJoin_SemanticMaterialInputs50.alpha built i)) ∧
    ∃ (before middle : host_wire.SemanticTranscript aspis_core.digest.LegacyHashFn)
      (z0 z1 : aspis_core.circle.SecureCirclePoint) (f25 f26 : Slice U8)
      (coeff : alloc.vec.Vec PV_RunJoin_ClaimThread48.Column),
      @host_wire.SemanticTranscript.challenge_reference_circle_point (types base) (selected base heap box ops) _ (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
        before 25#u8 f25=ok (.Ok z0,middle) ∧
      @host_wire.SemanticTranscript.challenge_reference_circle_point (types base) (selected base heap box ops) _ (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
        middle 26#u8 f26=ok (.Ok z1,built.transcript) ∧
      @prover.opening_coefficients (types base) (selected base heap box ops) .S2
        (alloc.vec.Vec.deref backend.messages)=ok coeff ∧
      @prover.opening_claim_bytes (types base) (selected base heap box ops) (alloc.vec.Vec.deref coeff)
        ⟨ProverRwDictionaryTower.fromW (ProverCommitNativeOps47.embedded
          (ProverCommitNativeOps47.normalize (PV_RunJoin_SemanticScalar50.raw z1.x))),
         ProverRwDictionaryTower.fromW (ProverCommitNativeOps47.embedded
          (ProverCommitNativeOps47.normalize (PV_RunJoin_SemanticScalar50.raw z1.y)))⟩=ok out.y1 := by
  have alpha := PV_RunJoin_MaterialAlphaProduced51.complete base heap box ops (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops)) commitInst public1 compiled
    noised maskOnly d g padding commitments nextCommitments hash .S2 built success
  obtain ⟨before,middle,z0,z1,f25,f26,h25,h26,hz,hx0,hy0,hx1,hy1,hpoint⟩ :=
    PV_RunJoin_MaterialPointOrigins51.complete base heap box ops (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops)) commitInst public1 compiled
      noised maskOnly d g padding commitments nextCommitments hash .S2 built success
  obtain ⟨canonical,coeff,hcoeff,hclaim⟩ := PV_RunJoin_PrepareClaimInputs51.complete base heap box ops .S2
    hash backend built out prepare
  rw [hpoint] at hclaim
  exact ⟨alpha,before,middle,z0,z1,f25,f26,coeff,h25,h26,hcoeff,hclaim⟩
#print axioms complete
end R1Z.PV_RunJoin_PrepareOrigins51
