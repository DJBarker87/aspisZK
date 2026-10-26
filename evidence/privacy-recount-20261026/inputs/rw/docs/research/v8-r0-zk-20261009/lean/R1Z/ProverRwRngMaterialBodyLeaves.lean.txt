import R1Z.ProverRwRngMaterialBodyTypes
open Aeneas Aeneas.Std Result ControlFlow
noncomputable section
namespace ProverRwRngMaterialBody
variable [TypeLeaves]
def core.result.Result.map_err {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F)
    (status : core.result.Result T E) (closure : O) : Result (core.result.Result T F) :=
  match status with
  | .Ok x => .ok (.Ok x)
  | .Err e => do
    let mapped ← inst.call_once closure e
    .ok (.Err mapped)
class LocalLeaves where
  f0 {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) :
  (Option T) → (Option T) → Result Bool
  f1 : std.io.error.Error → Result core.io.error.ErrorKind
  f2 {T : Type} (A : Type) (N : Std.Usize) :
  (alloc.vec.Vec T) → Result (core.result.Result (Array T N) (alloc.vec.Vec
    T))
  f3 : aspis_core.digest.LegacyHashFn → Result aspis_core.digest.LegacyHashFn
  f4 :
  aspis_core.digest.LegacyHashFn → (Slice (Slice Std.U8)) → Result (Array
    Std.U8 32#usize)
  f5 :
  aspis_core.field.wide_exact.WideExact → Result
    aspis_core.field.wide_exact.WideExact
  f6 : Result aspis_core.field.wide_exact.WideExact
  f7 : aspis_core.field.QM31 → aspis_core.field.QM31 → Result Bool
  f8 : Result aspis_core.field.QM31
  f9 : Result Std.U8
  f10 : Result Std.U8
  f11 : Result Std.U8
  f12 {Z : Type} {N : Std.Usize} (ZeroizeInst : zeroize.Zeroize Z) :
  (Array Z N) → Result (Array Z N)
  f13 {Z : Type} (DefaultIsZeroesInst : zeroize.DefaultIsZeroes Z) : Z → Result Z
  f14 {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) :
  (zeroize.Zeroizing Z) → Result (zeroize.Zeroizing Z)
  f15 {T : Type} {Z : Type} (coreconvertAsRefInst : core.convert.AsRef Z T)
  (ZeroizeInst : zeroize.Zeroize Z) :
  (zeroize.Zeroizing Z) → Result T
  f16 {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) :
  (zeroize.Zeroizing Z) → Result Z
  f17 {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) :
  Z → Result (zeroize.Zeroizing Z)
  f18 :
  Result (core.result.Result (alloc.vec.Vec aspis_statement.trace_v4.TraceCell)
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1)
  f19 :
  aspis_prover.state_only_hiding.SeedExpander → Std.Usize → (Array Bool
    1024#usize) → Result ((core.result.Result (alloc.vec.Vec
    aspis_core.field.QM31)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_prover.state_only_hiding.SeedExpander)
  f20 :
  aspis_prover.state_only_hiding.SeedExpander → Std.Usize → (Array Bool
    1024#usize) → Result ((core.result.Result (alloc.vec.Vec
    aspis_core.field.QM31)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_prover.state_only_hiding.SeedExpander)
  f21 :
  aspis_prover.state_only_hiding.SeedExpander → Std.Usize → (Array Bool
    1024#usize) → Result ((core.result.Result (Array (alloc.vec.Vec
    aspis_core.field.M31) 10#usize)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_prover.state_only_hiding.SeedExpander)
  f22 :
  aspis_prover.state_only_hiding.SeedExpander → Std.Usize → Result
    ((core.result.Result (alloc.vec.Vec aspis_core.field.M31)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_prover.state_only_hiding.SeedExpander)
  f23 : (Array Bool 1024#usize) → Result Std.Usize
  f24 :
  Result (core.result.Result (Array Bool 1024#usize)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError)
  f25 :
  aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets → (Slice
    (Slice Std.U8) → Result (Array Std.U8 32#usize)) →
    aspis_core.state_only_hiding.StateOnlyHidingContext → Result
    (core.result.Result (alloc.vec.Vec aspis_core.field.QM31)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError)
  f26 :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore → (Array
    Std.U8 32#usize) → (Array Std.U8 32#usize) → Result
    ((core.result.Result Bool std.io.error.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  f27 :
  aspis_statement.state_only_trace.StateOnlyTraceFoundation →
    aspis_prover.state_only_hiding.StateOnlyMaskMaterial → Result
    ((core.result.Result aspis_prover.state_only_hiding.AppliedStateOnlyMasks
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  f28 :
  Result (core.result.Result (Array Std.U16 64#usize)
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1)
  f29 :
  aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → Result
    (core.result.Result (alloc.vec.Vec Std.U8)
    aspis_core.state_only_prefix.r0.Error)
  f30 : (Slice aspis_core.field.QM31) → Result (Option aspis_core.field.QM31)
  f31 :
  aspis_statement.state_only_trace.StateOnlyTraceFoundation → Result
    aspis_statement.state_only_trace.StateOnlyTraceFoundation
  f32 :
  Result (core.result.Result host_commitment.EncodingDomain
    aspis_core.r0.Error)
  f33 {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (CommitmentsInst : host_semantic.Commitments
  T1) :
  aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public →
    aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
    → aspis_statement.state_only_trace.StateOnlyTraceFoundation → (Array
    (alloc.vec.Vec aspis_core.field.M31) 10#usize) → (Array
    aspis_core.field.QM31 1024#usize) → (Array aspis_core.field.QM31
    1024#usize) → (Array aspis_core.field.QM31 1024#usize) → T1 → H →
    transport.Variant → Result ((core.result.Result
    (host_semantic.BuiltSemantics H) r1_wire.Error) × T1)
  f34 :
  prover.Backend → (Slice aspis_core.field.QM31) → (Array
    aspis_core.field.QM31 1024#usize) → Result ((core.result.Result (Array
    Std.U8 32#usize) r1_wire.Error) × prover.Backend)
  f35 :
  prover.Backend → (Array (alloc.vec.Vec aspis_core.field.M31) 26#usize) →
    (Array aspis_core.field.QM31 1024#usize) → Result ((core.result.Result
    (Array Std.U8 32#usize) r1_wire.Error) × prover.Backend)
  f36 :
  aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public →
    transport.Variant → (Slice (Slice Std.U8) → Result (Array Std.U8
    32#usize)) → prover.Backend → (host_semantic.BuiltSemantics
    aspis_core.digest.LegacyHashFn) →
    (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
    aspis_core.state_only_hiding.StateOnlyHidingContext) → Result
    (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error)
  f37 :
  aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets →
    aspis_core.state_only_hiding.StateOnlyHidingContext → (Slice (Slice
    Std.U8) → Result (Array Std.U8 32#usize)) → Std.U8 → Result
    (core.result.Result host_commitment.PrivateSalts verifier.Error)
  f38 : r1_wire.Error → Result verifier.Error
  f39 :
  (Slice (alloc.vec.Vec aspis_core.field.M31)) → (Array (alloc.vec.Vec
    aspis_core.field.M31) 10#usize) → (Array aspis_core.field.QM31
    1024#usize) → (Array aspis_core.field.QM31 1024#usize) → (Array
    aspis_core.field.QM31 1024#usize) → (Array Std.U16 64#usize) → Result
    prover.MaskedFixtureAudit
  f40 :
  (Slice aspis_core.field.QM31) → Result (Array aspis_core.field.QM31
    1024#usize)
variable [LocalLeaves]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq := @LocalLeaves.f0 _ _
def std.io.error.Error.kind := @LocalLeaves.f1 _ _
def Array.Insts.CoreConvertTryFromVecVec.try_from := @LocalLeaves.f2 _ _
def aspis_core.digest.LegacyHashFn.Insts.CoreCloneClone.clone := @LocalLeaves.f3 _ _
def aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32.digest := @LocalLeaves.f4 _ _
def aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone.clone := @LocalLeaves.f5 _ _
def aspis_core.field.wide_exact.WideExact.ZERO := @LocalLeaves.f6 _ _
def aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq := @LocalLeaves.f7 _ _
def aspis_core.field.QM31.ZERO := @LocalLeaves.f8 _ _
def aspis_core.r0.merkle.C1_TAG := @LocalLeaves.f9 _ _
def aspis_core.r0.merkle.C2_TAG := @LocalLeaves.f10 _ _
def aspis_core.state_only_hiding.STATE_ONLY_HIDING_CONTEXT_VERSION := @LocalLeaves.f11 _ _
def Array.Insts.ZeroizeZeroize.zeroize := @LocalLeaves.f12 _ _
def zeroize.Zeroize.Blanket.zeroize := @LocalLeaves.f13 _ _
def zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize := @LocalLeaves.f14 _ _
def zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref := @LocalLeaves.f15 _ _
def zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref := @LocalLeaves.f16 _ _
def zeroize.Zeroizing.new := @LocalLeaves.f17 _ _
def aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1 := @LocalLeaves.f18 _ _
def aspis_prover.state_only_hiding.sample_mask_h1_padding := @LocalLeaves.f19 _ _
def aspis_prover.state_only_hiding.sample_mask_g := @LocalLeaves.f20 _ _
def aspis_prover.state_only_hiding.sample_mask_columns := @LocalLeaves.f21 _ _
def aspis_prover.state_only_hiding.sample_mask_cells := @LocalLeaves.f22 _ _
def aspis_prover.state_only_hiding.first_inactive_row := @LocalLeaves.f23 _ _
def aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows := @LocalLeaves.f24 _ _
def aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d := @LocalLeaves.f25 _ _
def aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible := @LocalLeaves.f26 _ _
def aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1 := @LocalLeaves.f27 _ _
def aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1 := @LocalLeaves.f28 _ _
def aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes := @LocalLeaves.f29 _ _
def aspis_statement.state_only_semantic.state_only_copy_helper_sum := @LocalLeaves.f30 _ _
def aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone := @LocalLeaves.f31 _ _
def host_commitment.EncodingDomain.new := @LocalLeaves.f32 _ _
def host_semantic.build_with_material := @LocalLeaves.f33 _ _
def prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2 := @LocalLeaves.f34 _ _
def prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1 := @LocalLeaves.f35 _ _
def prover.prove_from_semantics := @LocalLeaves.f36 _ _
def prover.derive_private_salts := @LocalLeaves.f37 _ _
def prover.semantic_error := @LocalLeaves.f38 _ _
def prover.audit_masks := @LocalLeaves.f39 _ _
def prover.fixed_k_column := @LocalLeaves.f40 _ _
end ProverRwRngMaterialBody
