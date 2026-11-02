import PV_EVH_NonceProver
import PV_EVH_OpMaterialFromEntropy
import PV_EVH_OpApplyMaterial
import PV_EVH_BuildSemantics
import PV_EVH_ProveSemantics
import PV_EVH_OpPrivateSalts
set_option autoImplicit false
noncomputable section
namespace PV_EVH_OpLeafInstall
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (FinishedView)
variable [ExternalTypes] [ExternalFuns]
/- Local source Result transport only. Every remaining source/runtime leaf,
formatting path, native observation link and actual success is still OPEN. -/

structure SemanticsCallees where
  prepare_opening_OPEN : ∀ (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn), PV_EVH_Prefix.P ((core.result.Result prover.PreparedOpening verifier.Error))
  finish_opening_OPEN : ∀ (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (prepared : prover.PreparedOpening)
  (folded_salts : host_commitment.PrivateSalts), PV_EVH_Prefix.P ((core.result.Result prover.Publication verifier.Error))
  publish_compact_OPEN : ∀ (variant : transport.Variant) (p : prover.Publication), PV_EVH_Prefix.P ((core.result.Result (alloc.vec.Vec Std.U8) verifier.Error))

structure SemanticsCompatible (c : SemanticsCallees) : Prop where
  prepare_opening_fixed : ∀ (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn), FinishedView (c.prepare_opening_OPEN variant hash backend sem) (prover.prepare_opening variant hash backend sem)
  finish_opening_fixed : ∀ (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (prepared : prover.PreparedOpening)
  (folded_salts : host_commitment.PrivateSalts), FinishedView (c.finish_opening_OPEN variant hash prepared folded_salts) (prover.finish_opening variant hash prepared folded_salts)
  publish_compact_fixed : ∀ (variant : transport.Variant) (p : prover.Publication), FinishedView (c.publish_compact_OPEN variant p) (prover.publish_compact variant p)

def installSemantics (c : SemanticsCallees) (saltCallees : PV_EVH_OpPrivateSalts.Callees) : PV_EVH_ProveSemantics.Callees where
  prepare_opening_OPEN := c.prepare_opening_OPEN
  derive_private_salts_OPEN := fun reserved context hash tag => PV_EVH_OpPrivateSalts.run reserved context hash tag saltCallees
  finish_opening_OPEN := c.finish_opening_OPEN
  publish_compact_OPEN := c.publish_compact_OPEN

theorem installSemantics_fixed (c : SemanticsCallees) (saltCallees : PV_EVH_OpPrivateSalts.Callees) (hc : SemanticsCompatible c) (h_saltCallees : PV_EVH_OpPrivateSalts.Compatible saltCallees) :
    PV_EVH_ProveSemantics.Compatible (installSemantics c saltCallees) where
  prepare_opening_fixed := hc.prepare_opening_fixed
  derive_private_salts_fixed := fun reserved context hash tag => PV_EVH_OpPrivateSalts.run_fixed reserved context hash tag saltCallees h_saltCallees
  finish_opening_fixed := hc.finish_opening_fixed
  publish_compact_fixed := hc.publish_compact_fixed

#print axioms installSemantics_fixed

structure WithCallees where
  op231_OPEN : ∀ (arg0 : aspis_statement.state_only_trace.StateOnlyTraceFoundation), PV_EVH_Prefix.P (aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  op134_OPEN : PV_EVH_Prefix.P ((core.result.Result (Array Std.U16 64#usize) aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1))
  derive_pool_v1_pair_forest_zero_factor_d_OPEN : ∀ (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext), PV_EVH_Prefix.P ((core.result.Result (alloc.vec.Vec aspis_core.field.QM31)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError))
  op36_OPEN : ∀ {T : Type} (A : Type) (N : Std.Usize) (arg0 : (alloc.vec.Vec T)), PV_EVH_Prefix.P ((core.result.Result (Array T N) (alloc.vec.Vec T)))
  fixed_k_column_OPEN : ∀ (values : Slice aspis_core.field.QM31), PV_EVH_Prefix.P ((Array aspis_core.field.QM31 1024#usize))
  audit_masks_OPEN : ∀ (c1 : Slice (alloc.vec.Vec aspis_core.field.M31))
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize)
  (masks : Array Std.U16 64#usize), PV_EVH_Prefix.P (prover.MaskedFixtureAudit)
  op82_OPEN : PV_EVH_Prefix.P (Std.U8)
  op83_OPEN : PV_EVH_Prefix.P (Std.U8)
  new_OPEN : PV_EVH_Prefix.P ((core.result.Result host_commitment.EncodingDomain
    aspis_core.r0.Error))
  op42_OPEN : PV_EVH_Prefix.P (aspis_core.field.wide_exact.WideExact)
  fromElem_OPEN : ∀ {T : Type} (inst : core.clone.Clone T) (value : T) (count : Usize), PV_EVH_Prefix.P (alloc.vec.Vec T)
  op230_OPEN : ∀ (arg0 : (Slice aspis_core.field.QM31)), PV_EVH_Prefix.P ((Option aspis_core.field.QM31))
  op64_OPEN : PV_EVH_Prefix.P (aspis_core.field.QM31)
  op8_OPEN : ∀ {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) (arg0 : (Option T)) (arg1 : (Option T)), PV_EVH_Prefix.P (Bool)

structure WithCompatible (c : WithCallees) : Prop where
  op231_fixed : ∀ (arg0 : aspis_statement.state_only_trace.StateOnlyTraceFoundation), FinishedView (c.op231_OPEN arg0) (aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone arg0)
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
  op83_fixed : FinishedView (c.op83_OPEN) (aspis_core.r0.merkle.C2_TAG)
  new_fixed : FinishedView (c.new_OPEN) (host_commitment.EncodingDomain.new)
  op42_fixed : FinishedView (c.op42_OPEN) (aspis_core.field.wide_exact.WideExact.ZERO)
  fromElem_fixed : ∀ {T : Type} (inst : core.clone.Clone T) (value : T) (count : Usize), FinishedView (c.fromElem_OPEN inst value count) (alloc.vec.from_elem inst value count)
  op230_fixed : ∀ (arg0 : (Slice aspis_core.field.QM31)), FinishedView (c.op230_OPEN arg0) (aspis_statement.state_only_semantic.state_only_copy_helper_sum arg0)
  op64_fixed : FinishedView (c.op64_OPEN) (aspis_core.field.QM31.ZERO)
  op8_fixed : ∀ {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) (arg0 : (Option T)) (arg1 : (Option T)), FinishedView (c.op8_OPEN cmpPartialEqInst arg0 arg1) (core.option.Option.Insts.CoreCmpPartialEqOption.eq cmpPartialEqInst arg0 arg1)

def installWith (c : WithCallees) (applyCallees : PV_EVH_OpApplyMaterial.Callees) (buildCallees : PV_EVH_BuildSemantics.Callees) (saltCallees : PV_EVH_OpPrivateSalts.Callees) (semanticCallees : SemanticsCallees) : PV_EVH_NonceWithAttempt.Callees where
  op231_OPEN := c.op231_OPEN
  apply_pool_v1_pair_forest_mask_material_v1_OPEN := fun trace material => PV_EVH_OpApplyMaterial.run trace material applyCallees
  op134_OPEN := c.op134_OPEN
  derive_pool_v1_pair_forest_zero_factor_d_OPEN := c.derive_pool_v1_pair_forest_zero_factor_d_OPEN
  op36_OPEN := c.op36_OPEN
  fixed_k_column_OPEN := c.fixed_k_column_OPEN
  audit_masks_OPEN := c.audit_masks_OPEN
  op82_OPEN := c.op82_OPEN
  derive_private_salts_OPEN := fun reserved context hash tag => PV_EVH_OpPrivateSalts.run reserved context hash tag saltCallees
  op83_OPEN := c.op83_OPEN
  new_OPEN := c.new_OPEN
  op42_OPEN := c.op42_OPEN
  fromElem_OPEN := c.fromElem_OPEN
  build_with_material_OPEN := fun aspis_coredigestDigest32Inst CommitmentsInst public1 compiled noised_semantic_c1 mask_only d g h1_padding commitments hash variant => PV_EVH_BuildSemantics.run aspis_coredigestDigest32Inst CommitmentsInst public1 compiled noised_semantic_c1 mask_only d g h1_padding commitments hash variant buildCallees
  op230_OPEN := c.op230_OPEN
  op64_OPEN := c.op64_OPEN
  op8_OPEN := c.op8_OPEN
  prove_from_semantics_OPEN := fun public1 variant hash backend sem salts => PV_EVH_ProveSemantics.run public1 variant hash backend sem salts (installSemantics semanticCallees saltCallees)

theorem installWith_fixed (c : WithCallees) (applyCallees : PV_EVH_OpApplyMaterial.Callees) (buildCallees : PV_EVH_BuildSemantics.Callees) (saltCallees : PV_EVH_OpPrivateSalts.Callees) (semanticCallees : SemanticsCallees) (hc : WithCompatible c) (h_applyCallees : PV_EVH_OpApplyMaterial.Compatible applyCallees) (h_buildCallees : PV_EVH_BuildSemantics.Compatible buildCallees) (h_saltCallees : PV_EVH_OpPrivateSalts.Compatible saltCallees) (h_semanticCallees : SemanticsCompatible semanticCallees) :
    PV_EVH_NonceWithAttempt.Compatible (installWith c applyCallees buildCallees saltCallees semanticCallees) where
  op231_fixed := hc.op231_fixed
  apply_pool_v1_pair_forest_mask_material_v1_fixed := fun trace material => PV_EVH_OpApplyMaterial.run_fixed trace material applyCallees h_applyCallees
  op134_fixed := hc.op134_fixed
  derive_pool_v1_pair_forest_zero_factor_d_fixed := hc.derive_pool_v1_pair_forest_zero_factor_d_fixed
  op36_fixed := hc.op36_fixed
  fixed_k_column_fixed := hc.fixed_k_column_fixed
  audit_masks_fixed := hc.audit_masks_fixed
  op82_fixed := hc.op82_fixed
  derive_private_salts_fixed := fun reserved context hash tag => PV_EVH_OpPrivateSalts.run_fixed reserved context hash tag saltCallees h_saltCallees
  op83_fixed := hc.op83_fixed
  new_fixed := hc.new_fixed
  op42_fixed := hc.op42_fixed
  fromElem_fixed := hc.fromElem_fixed
  build_with_material_fixed := fun aspis_coredigestDigest32Inst CommitmentsInst public1 compiled noised_semantic_c1 mask_only d g h1_padding commitments hash variant => PV_EVH_BuildSemantics.run_fixed aspis_coredigestDigest32Inst CommitmentsInst public1 compiled noised_semantic_c1 mask_only d g h1_padding commitments hash variant buildCallees h_buildCallees
  op230_fixed := hc.op230_fixed
  op64_fixed := hc.op64_fixed
  op8_fixed := hc.op8_fixed
  prove_from_semantics_fixed := fun public1 variant hash backend sem salts => PV_EVH_ProveSemantics.run_fixed public1 variant hash backend sem salts (installSemantics semanticCallees saltCallees) (installSemantics_fixed semanticCallees saltCallees h_semanticCallees h_saltCallees)

#print axioms installWith_fixed

structure ReserveCallees where
  arrayNe_OPEN : ∀ {T : Type} {N : Usize} (inst : core.cmp.PartialEq T T) (a b : Array T N), PV_EVH_Prefix.P (Bool)
  op112_OPEN : PV_EVH_Prefix.P (Std.U64)
  op113_OPEN : PV_EVH_Prefix.P (Std.U64)
  op127_OPEN : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), PV_EVH_Prefix.P (Z)
  op116_OPEN : ∀ (arg0 : aspis_core.state_only_hiding.StateOnlyHidingContext), PV_EVH_Prefix.P ((Array Std.U8 81#usize))
  op131_OPEN : ∀ {T : Type} {Z : Type} (coreconvertAsRefInst : core.convert.AsRef Z T)
      (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), PV_EVH_Prefix.P (T)
  hash_OPEN : ∀ (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (s : Slice (Slice U8)), PV_EVH_Prefix.P ((Array U8 32#usize))
  op128_OPEN : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : Z), PV_EVH_Prefix.P ((zeroize.Zeroizing Z))
  op130_OPEN : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), PV_EVH_Prefix.P ((zeroize.Zeroizing Z))

structure ReserveCompatible (c : ReserveCallees) : Prop where
  arrayNe_fixed : ∀ {T : Type} {N : Usize} (inst : core.cmp.PartialEq T T) (a b : Array T N), FinishedView (c.arrayNe_OPEN inst a b) (core.array.equality.PartialEqArray.ne inst a b)
  op112_fixed : FinishedView (c.op112_OPEN) (aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1)
  op113_fixed : FinishedView (c.op113_OPEN) (aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1)
  op127_fixed : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), FinishedView (c.op127_OPEN ZeroizeInst arg0) (zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref ZeroizeInst arg0)
  op116_fixed : ∀ (arg0 : aspis_core.state_only_hiding.StateOnlyHidingContext), FinishedView (c.op116_OPEN arg0) (aspis_core.state_only_hiding.StateOnlyHidingContext.encode arg0)
  op131_fixed : ∀ {T : Type} {Z : Type} (coreconvertAsRefInst : core.convert.AsRef Z T)
      (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), FinishedView (c.op131_OPEN coreconvertAsRefInst ZeroizeInst arg0) (zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref coreconvertAsRefInst ZeroizeInst arg0)
  hash_fixed : ∀ (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (s : Slice (Slice U8)), FinishedView (c.hash_OPEN hash s) (hash s)
  op128_fixed : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : Z), FinishedView (c.op128_OPEN ZeroizeInst arg0) (zeroize.Zeroizing.new ZeroizeInst arg0)
  op130_fixed : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), FinishedView (c.op130_OPEN ZeroizeInst arg0) (zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize ZeroizeInst arg0)

def installReserve (c : ReserveCallees) (materialCallees : PV_EVH_OpMaterialFromEntropy.Callees) : PV_EVH_NonceReserveBuild.Callees where
  arrayNe_OPEN := c.arrayNe_OPEN
  op112_OPEN := c.op112_OPEN
  op113_OPEN := c.op113_OPEN
  op127_OPEN := c.op127_OPEN
  build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref_OPEN := fun StateOnlyMaskNonceStoreInst hash precommit_binding context private_entropy nonce_store => PV_EVH_OpMaterialFromEntropy.run StateOnlyMaskNonceStoreInst hash precommit_binding context private_entropy nonce_store materialCallees
  op116_OPEN := c.op116_OPEN
  op131_OPEN := c.op131_OPEN
  hash_OPEN := c.hash_OPEN
  op128_OPEN := c.op128_OPEN
  op130_OPEN := c.op130_OPEN

theorem installReserve_fixed (c : ReserveCallees) (materialCallees : PV_EVH_OpMaterialFromEntropy.Callees) (hc : ReserveCompatible c) (h_materialCallees : PV_EVH_OpMaterialFromEntropy.Compatible materialCallees) :
    PV_EVH_NonceReserveBuild.Compatible (installReserve c materialCallees) where
  arrayNe_fixed := hc.arrayNe_fixed
  op112_fixed := hc.op112_fixed
  op113_fixed := hc.op113_fixed
  op127_fixed := hc.op127_fixed
  build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref_fixed := fun StateOnlyMaskNonceStoreInst hash precommit_binding context private_entropy nonce_store => PV_EVH_OpMaterialFromEntropy.run_fixed StateOnlyMaskNonceStoreInst hash precommit_binding context private_entropy nonce_store materialCallees h_materialCallees
  op116_fixed := hc.op116_fixed
  op131_fixed := hc.op131_fixed
  hash_fixed := hc.hash_fixed
  op128_fixed := hc.op128_fixed
  op130_fixed := hc.op130_fixed

#print axioms installReserve_fixed
end PV_EVH_OpLeafInstall
