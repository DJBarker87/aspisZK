# Caller reachability and current source requirement

Target not yet established. 163/99/262 becomes159/96/255 after the proved seven-field source erasure, then172/83/255 after13 exact pure entries. This is a sufficient extracted-source bound, not an exact native invocation denominator. All99 original open-operation rows are retained below. Native invocation traces/effects and positive feasible execution remain open.

| Op | Name | Current source requirement | Evidence |
|---:|---|---|---|
|3|`core.mem.take`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|4|`core.mem.drop`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|14|`std.fs.File.open`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|15|`std.fs.File.sync_all`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|16|`std.io.Write.write_all.default`|absent / not required|`R1Z.PDict_ReachCaller.op16_irrelevant`|
|18|`std.fs.File.Insts.StdIoWrite.write`|absent / not required|`R1Z.PDict_ReachCaller.op18_irrelevant`|
|22|`std.fs.OpenOptions.open`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|23|`std.io.error.Error.kind`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|25|`std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|26|`std.path.Path.join`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|28|`alloc.string.String.Insts.CoreConvertAsRefPath.as_ref`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|29|`std.path.PathBuf.Insts.CoreConvertAsRefPath.as_ref`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|30|`alloc.string.String.with_capacity`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|31|`alloc.string.String.push_str`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|32|`alloc.vec.Vec.try_reserve_exact`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|33|`alloc.vec.Vec.pop`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|34|`alloc.vec.Vec.is_empty`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|35|`alloc.vec.Vec.Insts.CoreDefaultDefault.default`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|36|`Array.Insts.CoreConvertTryFromVecVec.try_from`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|37|`aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq`|retained; selected source body|`R1Z.PDict_PureDictionary.op37_installed`|
|40|`aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone.clone`|retained; selected source body|`R1Z.PDict_PureDictionary.op40_installed`|
|41|`aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq`|retained; selected source body|`R1Z.PDict_PureDictionary.op41_installed`|
|43|`aspis_core.field.wide_exact.WideExact.impl.c0`|retained; selected source body|`R1Z.PDict_PureDictionary.op43_installed`|
|44|`aspis_core.field.wide_exact.WideExact.impl.c1`|retained; selected source body|`R1Z.PDict_PureDictionary.op44_installed`|
|49|`aspis_core.field.wide_exact.WideExact.to_limbs`|retained; selected source body|`R1Z.PDict_CodecDictionary.op49_installed`|
|50|`aspis_core.field.wide_exact.WideExact.from_le_bytes`|retained; selected source body|`R1Z.PDict_CodecDictionary.op50_installed`|
|51|`aspis_core.field.wide_exact.WideExact.to_le_bytes`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|60|`aspis_core.field.CM31.new`|retained; selected source body|`R1Z.PDict_PureDictionary.op60_installed`|
|71|`aspis_core.field.QM31.from_le_bytes`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|72|`aspis_core.field.QM31.write_le_bytes`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|77|`aspis_core.r0.domain.Point.Insts.CoreCloneClone.clone`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|78|`aspis_core.r0.domain.fibre_point`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|79|`aspis_core.r0.encoder.eval_message`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|80|`aspis_core.r0.fold.phi_inverse`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|81|`aspis_core.r0.heap.filled`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|82|`aspis_core.r0.merkle.C1_TAG`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|83|`aspis_core.r0.merkle.C2_TAG`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|84|`aspis_core.r0.merkle.leaf`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|85|`aspis_core.r0.Error.Insts.CoreFmtDebug.fmt`|absent / not required|`R1Z.PDict_ReachCaller.op85_irrelevant`|
|86|`aspis_core.r0.opening.LANES`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|100|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.neg`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|101|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.neg`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|105|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|107|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.try_inv`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|109|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.try_inv`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|110|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|111|`aspis_core.state_only_hiding.PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|114|`aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext.eq`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|117|`aspis_core.state_only_hiding.state_only_selected_mask_value`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|118|`aspis_core.state_only_prefix.r0.statement_points`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|120|`aspis_core.state_only_sumcheck.state_only_boundary_sum`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|121|`aspis_core.state_only_sumcheck.evaluate_state_only_polynomial`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|122|`Array.Insts.ZeroizeZeroize.zeroize`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|123|`zeroize.Zeroize.Blanket.zeroize`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|127|`zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|128|`zeroize.Zeroizing.new`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|129|`getrandom.fill`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|130|`zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|131|`zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|132|`aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|133|`aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_rows_v1`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|134|`aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|205|`sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.finalize_variable_core`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|208|`sha2.core_api.Sha256VarCore.Insts.DigestCore_apiUpdateCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80.update_blocks`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|209|`block_buffer.Eager.Insts.Block_bufferSealedSealed.split_blocks`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|212|`digest.digest.Digest.Blanket.finalize`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|215|`digest.core_api.wrapper.CoreWrapper.Insts.DigestFixedOutput.finalize_into`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|216|`digest.core_api.wrapper.CoreWrapper.Insts.DigestUpdate.update`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|217|`digest.core_api.wrapper.CoreWrapper.Insts.CoreDefaultDefault.default`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|219|`digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.DigestCore_apiFixedOutputCore.finalize_fixed_core`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|222|`aspis_statement.constraints_v4.multilinear_evaluate_qm31`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|223|`aspis_statement.logup.compress_tagged_tuple`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|224|`aspis_statement.pool_v1.pair_forest_semantic_oracle.build_pool_v1_pair_forest_copy_helper_v1`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|225|`aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.transition`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|226|`aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|227|`aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|228|`aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|229|`aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1.eq`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|230|`aspis_statement.state_only_semantic.state_only_copy_helper_sum`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|231|`aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|232|`aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.p_r1_check`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|235|`multiproof.LEAF_BITS`|retained; selected source body|`R1Z.PDict_PureDictionary.op235_installed`|
|236|`multiproof.MAX_BATCH`|retained; selected source body|`R1Z.PDict_PureDictionary.op236_installed`|
|239|`r1_wire.CLAIMS`|retained; selected source body|`R1Z.PDict_PureDictionary.op239_installed`|
|240|`r1_wire.LANES`|retained; selected source body|`R1Z.PDict_PureDictionary.op240_installed`|
|246|`multiproof.binary_parent`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|247|`trace.value`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|249|`sampler.gamma_sample`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|250|`sampler.ordinary_sample`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|251|`weights.Weights.materialize`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|252|`weights.Weights.new`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|253|`weights.Weights.raw`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|254|`weights.powers`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|255|`transport.Variant.coefficients`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|257|`host_work.map`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|258|`ct_pole.all_slots_clear`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|259|`sampler.circle_sample`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|
|260|`r1_wire.DOMAIN`|retained; selected source body|`R1Z.PDict_PureDictionary.op260_installed`|
|261|`std.fs.File.Insts.StdIoWrite.write_all`|retained; open|`reference path only in reachability.json; feasible execution unresolved`|

## Types

| ID | Type | Status |
|---:|---|---|
|3|std.io.error.Error|Native binding open; extracted owned reference and scoped native observations complete, full reachable/native/world quotient open|
|27|core.fmt.Formatter|Native binding open; full dictionary retyping plus store/path transport checked, whole caller carrier transport open|

26/28 native lower type values remain selected. File ownership/world and root refinement/headline premises remain unchanged. No new premises;13 pure source-entry obligations and three irrelevant open source callbacks removed from the stated source requirement.
