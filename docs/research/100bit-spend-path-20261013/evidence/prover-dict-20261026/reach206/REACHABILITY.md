# Caller dictionary reachability checkpoint

This is a partial Stage 1 checkpoint. Target not yet established. No positive execution-reachability theorem is claimed from a reference graph.

Historical: 163 selected / 99 open / 262 fields. Existing complete op85 erasure justifies 163 selected / 98 open / 261 source fields. The new seven-field bridge is NOT checked: 159 / 96 / 255 is a pending bound, not the final required denominator. Types remain 26 / 28; File ownership/world remains open.

Named premise effect: op85 source callback equality is unnecessary by the inherited `R1Z.PDict_ClientFormatterIndependent.client_erased`. New helper checks do not yet discharge op16/op18 at the full caller. Root RustProverRefinement conjunct 1 is retained unchanged.

## All 99 predecessor-open operations

| Op | Name | Reference path? | Execution classification / theorem |
|---:|---|---|---|
|3|`core.mem.take`|yes|Unresolved: reference path only|
|4|`core.mem.drop`|yes|Unresolved: reference path only|
|14|`std.fs.File.open`|yes|Unresolved: reference path only|
|15|`std.fs.File.sync_all`|yes|Unresolved: reference path only|
|16|`std.io.Write.write_all.default`|no|Unresolved: absent; caller bridge pending|
|18|`std.fs.File.Insts.StdIoWrite.write`|no|Unresolved: absent; caller bridge pending|
|22|`std.fs.OpenOptions.open`|yes|Unresolved: reference path only|
|23|`std.io.error.Error.kind`|yes|Unresolved: reference path only|
|25|`std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref`|yes|Unresolved: reference path only|
|26|`std.path.Path.join`|yes|Unresolved: reference path only|
|28|`alloc.string.String.Insts.CoreConvertAsRefPath.as_ref`|yes|Unresolved: reference path only|
|29|`std.path.PathBuf.Insts.CoreConvertAsRefPath.as_ref`|yes|Unresolved: reference path only|
|30|`alloc.string.String.with_capacity`|yes|Unresolved: reference path only|
|31|`alloc.string.String.push_str`|yes|Unresolved: reference path only|
|32|`alloc.vec.Vec.try_reserve_exact`|yes|Unresolved: reference path only|
|33|`alloc.vec.Vec.pop`|yes|Unresolved: reference path only|
|34|`alloc.vec.Vec.is_empty`|yes|Unresolved: reference path only|
|35|`alloc.vec.Vec.Insts.CoreDefaultDefault.default`|yes|Unresolved: reference path only|
|36|`Array.Insts.CoreConvertTryFromVecVec.try_from`|yes|Unresolved: reference path only|
|37|`aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq`|yes|Unresolved: reference path only|
|40|`aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone.clone`|yes|Unresolved: reference path only|
|41|`aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq`|yes|Unresolved: reference path only|
|43|`aspis_core.field.wide_exact.WideExact.impl.c0`|yes|Unresolved: reference path only|
|44|`aspis_core.field.wide_exact.WideExact.impl.c1`|yes|Unresolved: reference path only|
|49|`aspis_core.field.wide_exact.WideExact.to_limbs`|yes|Unresolved: reference path only|
|50|`aspis_core.field.wide_exact.WideExact.from_le_bytes`|yes|Unresolved: reference path only|
|51|`aspis_core.field.wide_exact.WideExact.to_le_bytes`|yes|Unresolved: reference path only|
|60|`aspis_core.field.CM31.new`|yes|Unresolved: reference path only|
|71|`aspis_core.field.QM31.from_le_bytes`|yes|Unresolved: reference path only|
|72|`aspis_core.field.QM31.write_le_bytes`|yes|Unresolved: reference path only|
|77|`aspis_core.r0.domain.Point.Insts.CoreCloneClone.clone`|yes|Unresolved: reference path only|
|78|`aspis_core.r0.domain.fibre_point`|yes|Unresolved: reference path only|
|79|`aspis_core.r0.encoder.eval_message`|yes|Unresolved: reference path only|
|80|`aspis_core.r0.fold.phi_inverse`|yes|Unresolved: reference path only|
|81|`aspis_core.r0.heap.filled`|yes|Unresolved: reference path only|
|82|`aspis_core.r0.merkle.C1_TAG`|yes|Unresolved: reference path only|
|83|`aspis_core.r0.merkle.C2_TAG`|yes|Unresolved: reference path only|
|84|`aspis_core.r0.merkle.leaf`|yes|Unresolved: reference path only|
|85|`aspis_core.r0.Error.Insts.CoreFmtDebug.fmt`|no|No source dependence: `R1Z.PDict_ClientFormatterIndependent.client_erased`|
|86|`aspis_core.r0.opening.LANES`|yes|Unresolved: reference path only|
|100|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.neg`|yes|Unresolved: reference path only|
|101|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.neg`|yes|Unresolved: reference path only|
|105|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv`|yes|Unresolved: reference path only|
|107|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.try_inv`|yes|Unresolved: reference path only|
|109|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.try_inv`|yes|Unresolved: reference path only|
|110|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31`|yes|Unresolved: reference path only|
|111|`aspis_core.state_only_hiding.PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT`|yes|Unresolved: reference path only|
|114|`aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext.eq`|yes|Unresolved: reference path only|
|117|`aspis_core.state_only_hiding.state_only_selected_mask_value`|yes|Unresolved: reference path only|
|118|`aspis_core.state_only_prefix.r0.statement_points`|yes|Unresolved: reference path only|
|120|`aspis_core.state_only_sumcheck.state_only_boundary_sum`|yes|Unresolved: reference path only|
|121|`aspis_core.state_only_sumcheck.evaluate_state_only_polynomial`|yes|Unresolved: reference path only|
|122|`Array.Insts.ZeroizeZeroize.zeroize`|yes|Unresolved: reference path only|
|123|`zeroize.Zeroize.Blanket.zeroize`|yes|Unresolved: reference path only|
|127|`zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref`|yes|Unresolved: reference path only|
|128|`zeroize.Zeroizing.new`|yes|Unresolved: reference path only|
|129|`getrandom.fill`|yes|Unresolved: reference path only|
|130|`zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize`|yes|Unresolved: reference path only|
|131|`zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref`|yes|Unresolved: reference path only|
|132|`aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1`|yes|Unresolved: reference path only|
|133|`aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_rows_v1`|yes|Unresolved: reference path only|
|134|`aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1`|yes|Unresolved: reference path only|
|205|`sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.finalize_variable_core`|yes|Unresolved: reference path only|
|208|`sha2.core_api.Sha256VarCore.Insts.DigestCore_apiUpdateCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80.update_blocks`|yes|Unresolved: reference path only|
|209|`block_buffer.Eager.Insts.Block_bufferSealedSealed.split_blocks`|yes|Unresolved: reference path only|
|212|`digest.digest.Digest.Blanket.finalize`|yes|Unresolved: reference path only|
|215|`digest.core_api.wrapper.CoreWrapper.Insts.DigestFixedOutput.finalize_into`|yes|Unresolved: reference path only|
|216|`digest.core_api.wrapper.CoreWrapper.Insts.DigestUpdate.update`|yes|Unresolved: reference path only|
|217|`digest.core_api.wrapper.CoreWrapper.Insts.CoreDefaultDefault.default`|yes|Unresolved: reference path only|
|219|`digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.DigestCore_apiFixedOutputCore.finalize_fixed_core`|yes|Unresolved: reference path only|
|222|`aspis_statement.constraints_v4.multilinear_evaluate_qm31`|yes|Unresolved: reference path only|
|223|`aspis_statement.logup.compress_tagged_tuple`|yes|Unresolved: reference path only|
|224|`aspis_statement.pool_v1.pair_forest_semantic_oracle.build_pool_v1_pair_forest_copy_helper_v1`|yes|Unresolved: reference path only|
|225|`aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.transition`|yes|Unresolved: reference path only|
|226|`aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes`|yes|Unresolved: reference path only|
|227|`aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31`|yes|Unresolved: reference path only|
|228|`aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1`|yes|Unresolved: reference path only|
|229|`aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1.eq`|yes|Unresolved: reference path only|
|230|`aspis_statement.state_only_semantic.state_only_copy_helper_sum`|yes|Unresolved: reference path only|
|231|`aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone`|yes|Unresolved: reference path only|
|232|`aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.p_r1_check`|yes|Unresolved: reference path only|
|235|`multiproof.LEAF_BITS`|yes|Unresolved: reference path only|
|236|`multiproof.MAX_BATCH`|yes|Unresolved: reference path only|
|239|`r1_wire.CLAIMS`|yes|Unresolved: reference path only|
|240|`r1_wire.LANES`|yes|Unresolved: reference path only|
|246|`multiproof.binary_parent`|yes|Unresolved: reference path only|
|247|`trace.value`|yes|Unresolved: reference path only|
|249|`sampler.gamma_sample`|yes|Unresolved: reference path only|
|250|`sampler.ordinary_sample`|yes|Unresolved: reference path only|
|251|`weights.Weights.materialize`|yes|Unresolved: reference path only|
|252|`weights.Weights.new`|yes|Unresolved: reference path only|
|253|`weights.Weights.raw`|yes|Unresolved: reference path only|
|254|`weights.powers`|yes|Unresolved: reference path only|
|255|`transport.Variant.coefficients`|yes|Unresolved: reference path only|
|257|`host_work.map`|yes|Unresolved: reference path only|
|258|`ct_pole.all_slots_clear`|yes|Unresolved: reference path only|
|259|`sampler.circle_sample`|yes|Unresolved: reference path only|
|260|`r1_wire.DOMAIN`|yes|Unresolved: reference path only|
|261|`std.fs.File.Insts.StdIoWrite.write_all`|yes|Unresolved: reference path only|

## Open types

| Type | Representation | Status |
|---:|---|---|
|3|`std.io.error.Error`|retained: File error results and kind consumed; no owned-reference/native transport yet|
|27|`core.fmt.Formatter`|retained type transport: op85 erased; changing carrier also changes generic trait dictionaries; J20600/J20601 rejected|

Reference paths and source hashes: `reachability.json`. Lean raw inputs, diagnostics, time, dependencies and axioms: `206*-receipt.json` / `lean-summary.json`. No Kani run, production change, native error/world law, or frozen release replay is claimed.
