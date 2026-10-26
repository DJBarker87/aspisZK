# Whole caller source reachability

Target not yet established. Full extracted caller results are independent of fields 13,16,17,18,85,124,238 simultaneously and separately. The proof retains all input arguments and all Result success/error/divergence branches. It does not instrument native effects or prove an executable witness for referenced operations.

Before: 163 selected / 99 open / 262. After source-field erasure: **159 selected / 96 open / 255 required source fields**. This is a sufficient source-dependency denominator, not an exact feasible-native-invocation count. Types remain 26/28. Root premises removed: 0.

| Op | Name | Source dependence | Theorem or reference |
|---:|---|---|---|
|3|`core.mem.take`|retained; feasible execution unresolved|reference path in reachability.json|
|4|`core.mem.drop`|retained; feasible execution unresolved|reference path in reachability.json|
|14|`std.fs.File.open`|retained; feasible execution unresolved|reference path in reachability.json|
|15|`std.fs.File.sync_all`|retained; feasible execution unresolved|reference path in reachability.json|
|16|`std.io.Write.write_all.default`|absent|R1Z.PDict_ReachCaller.op16_irrelevant|
|18|`std.fs.File.Insts.StdIoWrite.write`|absent|R1Z.PDict_ReachCaller.op18_irrelevant|
|22|`std.fs.OpenOptions.open`|retained; feasible execution unresolved|reference path in reachability.json|
|23|`std.io.error.Error.kind`|retained; feasible execution unresolved|reference path in reachability.json|
|25|`std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref`|retained; feasible execution unresolved|reference path in reachability.json|
|26|`std.path.Path.join`|retained; feasible execution unresolved|reference path in reachability.json|
|28|`alloc.string.String.Insts.CoreConvertAsRefPath.as_ref`|retained; feasible execution unresolved|reference path in reachability.json|
|29|`std.path.PathBuf.Insts.CoreConvertAsRefPath.as_ref`|retained; feasible execution unresolved|reference path in reachability.json|
|30|`alloc.string.String.with_capacity`|retained; feasible execution unresolved|reference path in reachability.json|
|31|`alloc.string.String.push_str`|retained; feasible execution unresolved|reference path in reachability.json|
|32|`alloc.vec.Vec.try_reserve_exact`|retained; feasible execution unresolved|reference path in reachability.json|
|33|`alloc.vec.Vec.pop`|retained; feasible execution unresolved|reference path in reachability.json|
|34|`alloc.vec.Vec.is_empty`|retained; feasible execution unresolved|reference path in reachability.json|
|35|`alloc.vec.Vec.Insts.CoreDefaultDefault.default`|retained; feasible execution unresolved|reference path in reachability.json|
|36|`Array.Insts.CoreConvertTryFromVecVec.try_from`|retained; feasible execution unresolved|reference path in reachability.json|
|37|`aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq`|retained; feasible execution unresolved|reference path in reachability.json|
|40|`aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone.clone`|retained; feasible execution unresolved|reference path in reachability.json|
|41|`aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq`|retained; feasible execution unresolved|reference path in reachability.json|
|43|`aspis_core.field.wide_exact.WideExact.impl.c0`|retained; feasible execution unresolved|reference path in reachability.json|
|44|`aspis_core.field.wide_exact.WideExact.impl.c1`|retained; feasible execution unresolved|reference path in reachability.json|
|49|`aspis_core.field.wide_exact.WideExact.to_limbs`|retained; feasible execution unresolved|reference path in reachability.json|
|50|`aspis_core.field.wide_exact.WideExact.from_le_bytes`|retained; feasible execution unresolved|reference path in reachability.json|
|51|`aspis_core.field.wide_exact.WideExact.to_le_bytes`|retained; feasible execution unresolved|reference path in reachability.json|
|60|`aspis_core.field.CM31.new`|retained; feasible execution unresolved|reference path in reachability.json|
|71|`aspis_core.field.QM31.from_le_bytes`|retained; feasible execution unresolved|reference path in reachability.json|
|72|`aspis_core.field.QM31.write_le_bytes`|retained; feasible execution unresolved|reference path in reachability.json|
|77|`aspis_core.r0.domain.Point.Insts.CoreCloneClone.clone`|retained; feasible execution unresolved|reference path in reachability.json|
|78|`aspis_core.r0.domain.fibre_point`|retained; feasible execution unresolved|reference path in reachability.json|
|79|`aspis_core.r0.encoder.eval_message`|retained; feasible execution unresolved|reference path in reachability.json|
|80|`aspis_core.r0.fold.phi_inverse`|retained; feasible execution unresolved|reference path in reachability.json|
|81|`aspis_core.r0.heap.filled`|retained; feasible execution unresolved|reference path in reachability.json|
|82|`aspis_core.r0.merkle.C1_TAG`|retained; feasible execution unresolved|reference path in reachability.json|
|83|`aspis_core.r0.merkle.C2_TAG`|retained; feasible execution unresolved|reference path in reachability.json|
|84|`aspis_core.r0.merkle.leaf`|retained; feasible execution unresolved|reference path in reachability.json|
|85|`aspis_core.r0.Error.Insts.CoreFmtDebug.fmt`|absent|R1Z.PDict_ReachCaller.op85_irrelevant|
|86|`aspis_core.r0.opening.LANES`|retained; feasible execution unresolved|reference path in reachability.json|
|100|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.neg`|retained; feasible execution unresolved|reference path in reachability.json|
|101|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.neg`|retained; feasible execution unresolved|reference path in reachability.json|
|105|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv`|retained; feasible execution unresolved|reference path in reachability.json|
|107|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.try_inv`|retained; feasible execution unresolved|reference path in reachability.json|
|109|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.try_inv`|retained; feasible execution unresolved|reference path in reachability.json|
|110|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31`|retained; feasible execution unresolved|reference path in reachability.json|
|111|`aspis_core.state_only_hiding.PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT`|retained; feasible execution unresolved|reference path in reachability.json|
|114|`aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext.eq`|retained; feasible execution unresolved|reference path in reachability.json|
|117|`aspis_core.state_only_hiding.state_only_selected_mask_value`|retained; feasible execution unresolved|reference path in reachability.json|
|118|`aspis_core.state_only_prefix.r0.statement_points`|retained; feasible execution unresolved|reference path in reachability.json|
|120|`aspis_core.state_only_sumcheck.state_only_boundary_sum`|retained; feasible execution unresolved|reference path in reachability.json|
|121|`aspis_core.state_only_sumcheck.evaluate_state_only_polynomial`|retained; feasible execution unresolved|reference path in reachability.json|
|122|`Array.Insts.ZeroizeZeroize.zeroize`|retained; feasible execution unresolved|reference path in reachability.json|
|123|`zeroize.Zeroize.Blanket.zeroize`|retained; feasible execution unresolved|reference path in reachability.json|
|127|`zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref`|retained; feasible execution unresolved|reference path in reachability.json|
|128|`zeroize.Zeroizing.new`|retained; feasible execution unresolved|reference path in reachability.json|
|129|`getrandom.fill`|retained; feasible execution unresolved|reference path in reachability.json|
|130|`zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize`|retained; feasible execution unresolved|reference path in reachability.json|
|131|`zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref`|retained; feasible execution unresolved|reference path in reachability.json|
|132|`aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1`|retained; feasible execution unresolved|reference path in reachability.json|
|133|`aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_rows_v1`|retained; feasible execution unresolved|reference path in reachability.json|
|134|`aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1`|retained; feasible execution unresolved|reference path in reachability.json|
|205|`sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.finalize_variable_core`|retained; feasible execution unresolved|reference path in reachability.json|
|208|`sha2.core_api.Sha256VarCore.Insts.DigestCore_apiUpdateCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80.update_blocks`|retained; feasible execution unresolved|reference path in reachability.json|
|209|`block_buffer.Eager.Insts.Block_bufferSealedSealed.split_blocks`|retained; feasible execution unresolved|reference path in reachability.json|
|212|`digest.digest.Digest.Blanket.finalize`|retained; feasible execution unresolved|reference path in reachability.json|
|215|`digest.core_api.wrapper.CoreWrapper.Insts.DigestFixedOutput.finalize_into`|retained; feasible execution unresolved|reference path in reachability.json|
|216|`digest.core_api.wrapper.CoreWrapper.Insts.DigestUpdate.update`|retained; feasible execution unresolved|reference path in reachability.json|
|217|`digest.core_api.wrapper.CoreWrapper.Insts.CoreDefaultDefault.default`|retained; feasible execution unresolved|reference path in reachability.json|
|219|`digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.DigestCore_apiFixedOutputCore.finalize_fixed_core`|retained; feasible execution unresolved|reference path in reachability.json|
|222|`aspis_statement.constraints_v4.multilinear_evaluate_qm31`|retained; feasible execution unresolved|reference path in reachability.json|
|223|`aspis_statement.logup.compress_tagged_tuple`|retained; feasible execution unresolved|reference path in reachability.json|
|224|`aspis_statement.pool_v1.pair_forest_semantic_oracle.build_pool_v1_pair_forest_copy_helper_v1`|retained; feasible execution unresolved|reference path in reachability.json|
|225|`aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.transition`|retained; feasible execution unresolved|reference path in reachability.json|
|226|`aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes`|retained; feasible execution unresolved|reference path in reachability.json|
|227|`aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31`|retained; feasible execution unresolved|reference path in reachability.json|
|228|`aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1`|retained; feasible execution unresolved|reference path in reachability.json|
|229|`aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1.eq`|retained; feasible execution unresolved|reference path in reachability.json|
|230|`aspis_statement.state_only_semantic.state_only_copy_helper_sum`|retained; feasible execution unresolved|reference path in reachability.json|
|231|`aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone`|retained; feasible execution unresolved|reference path in reachability.json|
|232|`aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.p_r1_check`|retained; feasible execution unresolved|reference path in reachability.json|
|235|`multiproof.LEAF_BITS`|retained; feasible execution unresolved|reference path in reachability.json|
|236|`multiproof.MAX_BATCH`|retained; feasible execution unresolved|reference path in reachability.json|
|239|`r1_wire.CLAIMS`|retained; feasible execution unresolved|reference path in reachability.json|
|240|`r1_wire.LANES`|retained; feasible execution unresolved|reference path in reachability.json|
|246|`multiproof.binary_parent`|retained; feasible execution unresolved|reference path in reachability.json|
|247|`trace.value`|retained; feasible execution unresolved|reference path in reachability.json|
|249|`sampler.gamma_sample`|retained; feasible execution unresolved|reference path in reachability.json|
|250|`sampler.ordinary_sample`|retained; feasible execution unresolved|reference path in reachability.json|
|251|`weights.Weights.materialize`|retained; feasible execution unresolved|reference path in reachability.json|
|252|`weights.Weights.new`|retained; feasible execution unresolved|reference path in reachability.json|
|253|`weights.Weights.raw`|retained; feasible execution unresolved|reference path in reachability.json|
|254|`weights.powers`|retained; feasible execution unresolved|reference path in reachability.json|
|255|`transport.Variant.coefficients`|retained; feasible execution unresolved|reference path in reachability.json|
|257|`host_work.map`|retained; feasible execution unresolved|reference path in reachability.json|
|258|`ct_pole.all_slots_clear`|retained; feasible execution unresolved|reference path in reachability.json|
|259|`sampler.circle_sample`|retained; feasible execution unresolved|reference path in reachability.json|
|260|`r1_wire.DOMAIN`|retained; feasible execution unresolved|reference path in reachability.json|
|261|`std.fs.File.Insts.StdIoWrite.write_all`|retained; feasible execution unresolved|reference path in reachability.json|

## Types

| ID | Type | Status |
|---:|---|---|
|3|std.io.error.Error|Open; reachable source error values and kind observation; dynamic payload adequacy retained|
|27|core.fmt.Formatter|Open native carrier; op85 erased, generic dictionary carrier transport retained|

File value association is installed; OS ownership and world transport remain open. No new premises; source op16/op18/op85 callback equations removed from caller requirement. Previously selected off-route fields13/17/124/238 no longer required here. No root privacy premise removed.
