import PV_EVH_MaskedWithAttempt
import PV_EVH_ReserveBuild
set_option autoImplicit false
noncomputable section
namespace PV_EVH_ReserveJoin
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]

/-- The eighteen remaining with-attempt callees. ReserveBuild itself has been
expanded; this does not assert that its eleven own callees are implemented. -/
structure Callees where
  op231_OPEN : ∀ (arg0 : aspis_statement.state_only_trace.StateOnlyTraceFoundation), P (aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  apply_pool_v1_pair_forest_mask_material_v1_OPEN : ∀ (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial), P (((core.result.Result
    aspis_prover.state_only_hiding.AppliedStateOnlyMasks
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_statement.state_only_trace.StateOnlyTraceFoundation))
  op134_OPEN : P ((core.result.Result (Array Std.U16 64#usize) aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1))
  derive_pool_v1_pair_forest_zero_factor_d_OPEN : ∀ (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext), P ((core.result.Result (alloc.vec.Vec aspis_core.field.QM31)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError))
  op36_OPEN : ∀ {T : Type} (A : Type) (N : Std.Usize) (arg0 : (alloc.vec.Vec T)), P ((core.result.Result (Array T N) (alloc.vec.Vec T)))
  fixed_k_column_OPEN : ∀ (values : Slice aspis_core.field.QM31), P ((Array aspis_core.field.QM31 1024#usize))
  audit_masks_OPEN : ∀ (c1 : Slice (alloc.vec.Vec aspis_core.field.M31))
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize)
  (masks : Array Std.U16 64#usize), P (prover.MaskedFixtureAudit)
  op82_OPEN : P (Std.U8)
  derive_private_salts_OPEN : ∀ (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8), P ((core.result.Result host_commitment.PrivateSalts verifier.Error))
  op83_OPEN : P (Std.U8)
  new_OPEN : P ((core.result.Result host_commitment.EncodingDomain
    aspis_core.r0.Error))
  op42_OPEN : P (aspis_core.field.wide_exact.WideExact)
  fromElem_OPEN : ∀ {T : Type} (inst : core.clone.Clone T) (value : T) (count : Usize), P (alloc.vec.Vec T)
  build_with_material_OPEN : ∀ {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (CommitmentsInst : host_semantic.Commitments
  T1)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (noised_semantic_c1 :
  aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize) (commitments : T1)
  (hash : H) (variant : transport.Variant), P (((core.result.Result (host_semantic.BuiltSemantics H) r1_wire.Error)
    × T1))
  op230_OPEN : ∀ (arg0 : (Slice aspis_core.field.QM31)), P ((Option aspis_core.field.QM31))
  op64_OPEN : P (aspis_core.field.QM31)
  op8_OPEN : ∀ {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) (arg0 : (Option T)) (arg1 : (Option T)), P (Bool)
  prove_from_semantics_OPEN : ∀ (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
  (salts : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
  aspis_core.state_only_hiding.StateOnlyHidingContext)), P ((core.result.Result (alloc.vec.Vec Std.U8) verifier.Error))

structure Compatible (c : Callees) : Prop where
  op231_fixed : ∀ (arg0 : aspis_statement.state_only_trace.StateOnlyTraceFoundation), FinishedView (c.op231_OPEN arg0) (aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone arg0)
  apply_pool_v1_pair_forest_mask_material_v1_fixed : ∀ (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial), FinishedView (c.apply_pool_v1_pair_forest_mask_material_v1_OPEN trace material) (aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1 trace material)
  op134_fixed : FinishedView (c.op134_OPEN) (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1)
  derive_pool_v1_pair_forest_zero_factor_d_fixed : ∀ (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext), FinishedView (c.derive_pool_v1_pair_forest_zero_factor_d_OPEN self hash context) (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d self hash context)
  op36_fixed : ∀ {T : Type} (A : Type) (N : Std.Usize) (arg0 : (alloc.vec.Vec T)), FinishedView (c.op36_OPEN A N arg0) (Array.Insts.CoreConvertTryFromVecVec.try_from A N arg0)
  fixed_k_column_fixed : ∀ (values : Slice aspis_core.field.QM31), FinishedView (c.fixed_k_column_OPEN values) (prover.fixed_k_column values)
  audit_masks_fixed : ∀ (c1 : Slice (alloc.vec.Vec aspis_core.field.M31))
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize)
  (masks : Array Std.U16 64#usize), FinishedView (c.audit_masks_OPEN c1 mask_only d g h1_padding masks) (prover.audit_masks c1 mask_only d g h1_padding masks)
  op82_fixed : FinishedView (c.op82_OPEN) (aspis_core.r0.merkle.C1_TAG)
  derive_private_salts_fixed : ∀ (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8), FinishedView (c.derive_private_salts_OPEN reserved context hash tag) (prover.derive_private_salts reserved context hash tag)
  op83_fixed : FinishedView (c.op83_OPEN) (aspis_core.r0.merkle.C2_TAG)
  new_fixed : FinishedView (c.new_OPEN) (host_commitment.EncodingDomain.new)
  op42_fixed : FinishedView (c.op42_OPEN) (aspis_core.field.wide_exact.WideExact.ZERO)
  fromElem_fixed : ∀ {T : Type} (inst : core.clone.Clone T) (value : T) (count : Usize), FinishedView (c.fromElem_OPEN inst value count) (alloc.vec.from_elem inst value count)
  build_with_material_fixed : ∀ {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (CommitmentsInst : host_semantic.Commitments
  T1)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (noised_semantic_c1 :
  aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize) (commitments : T1)
  (hash : H) (variant : transport.Variant), FinishedView (c.build_with_material_OPEN aspis_coredigestDigest32Inst CommitmentsInst public1 compiled noised_semantic_c1 mask_only d g h1_padding commitments hash variant) (host_semantic.build_with_material aspis_coredigestDigest32Inst CommitmentsInst public1 compiled noised_semantic_c1 mask_only d g h1_padding commitments hash variant)
  op230_fixed : ∀ (arg0 : (Slice aspis_core.field.QM31)), FinishedView (c.op230_OPEN arg0) (aspis_statement.state_only_semantic.state_only_copy_helper_sum arg0)
  op64_fixed : FinishedView (c.op64_OPEN) (aspis_core.field.QM31.ZERO)
  op8_fixed : ∀ {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) (arg0 : (Option T)) (arg1 : (Option T)), FinishedView (c.op8_OPEN cmpPartialEqInst arg0 arg1) (core.option.Option.Insts.CoreCmpPartialEqOption.eq cmpPartialEqInst arg0 arg1)
  prove_from_semantics_fixed : ∀ (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
  (salts : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
  aspis_core.state_only_hiding.StateOnlyHidingContext)), FinishedView (c.prove_from_semantics_OPEN public1 variant hash backend sem salts) (prover.prove_from_semantics public1 variant hash backend sem salts)

def install (c : Callees) (r : PV_EVH_ReserveBuild.Callees) : PV_EVH_MaskedWithAttempt.Callees where
  op231_OPEN := c.op231_OPEN
  apply_pool_v1_pair_forest_mask_material_v1_OPEN := c.apply_pool_v1_pair_forest_mask_material_v1_OPEN
  op134_OPEN := c.op134_OPEN
  derive_pool_v1_pair_forest_zero_factor_d_OPEN := c.derive_pool_v1_pair_forest_zero_factor_d_OPEN
  op36_OPEN := c.op36_OPEN
  fixed_k_column_OPEN := c.fixed_k_column_OPEN
  audit_masks_OPEN := c.audit_masks_OPEN
  op82_OPEN := c.op82_OPEN
  derive_private_salts_OPEN := c.derive_private_salts_OPEN
  op83_OPEN := c.op83_OPEN
  new_OPEN := c.new_OPEN
  op42_OPEN := c.op42_OPEN
  fromElem_OPEN := c.fromElem_OPEN
  build_with_material_OPEN := c.build_with_material_OPEN
  op230_OPEN := c.op230_OPEN
  op64_OPEN := c.op64_OPEN
  op8_OPEN := c.op8_OPEN
  prove_from_semantics_OPEN := c.prove_from_semantics_OPEN
  reserve_and_build_pool_v1_pair_forest_mask_material_v1_OPEN := fun inst self hash binding context store =>
    PV_EVH_ReserveBuild.run inst self hash binding context store r

theorem install_fixed (c : Callees) (r : PV_EVH_ReserveBuild.Callees)
    (hc : Compatible c) (hr : PV_EVH_ReserveBuild.Compatible r) :
    PV_EVH_MaskedWithAttempt.Compatible (install c r) where
  op231_fixed := hc.op231_fixed
  apply_pool_v1_pair_forest_mask_material_v1_fixed := hc.apply_pool_v1_pair_forest_mask_material_v1_fixed
  op134_fixed := hc.op134_fixed
  derive_pool_v1_pair_forest_zero_factor_d_fixed := hc.derive_pool_v1_pair_forest_zero_factor_d_fixed
  op36_fixed := hc.op36_fixed
  fixed_k_column_fixed := hc.fixed_k_column_fixed
  audit_masks_fixed := hc.audit_masks_fixed
  op82_fixed := hc.op82_fixed
  derive_private_salts_fixed := hc.derive_private_salts_fixed
  op83_fixed := hc.op83_fixed
  new_fixed := hc.new_fixed
  op42_fixed := hc.op42_fixed
  fromElem_fixed := hc.fromElem_fixed
  build_with_material_fixed := hc.build_with_material_fixed
  op230_fixed := hc.op230_fixed
  op64_fixed := hc.op64_fixed
  op8_fixed := hc.op8_fixed
  prove_from_semantics_fixed := hc.prove_from_semantics_fixed
  reserve_and_build_pool_v1_pair_forest_mask_material_v1_fixed := fun inst self hash binding context store =>
    PV_EVH_ReserveBuild.run_fixed inst self hash binding context store r hr

#print axioms install_fixed
end PV_EVH_ReserveJoin
