# Entry and reachability table

Unchanged:172 selected /83 open /255 sufficient source fields; exact feasible-native invocation denominator unestablished. Transport proofs do not install source operation bodies or native types. Root premises removed:0. Ledger rows refer to research revision `e97cb3923c111d0c3f49968bd76ba05417d158c7`.

| Field | Operation | Required source bound | Selection | Ledger |
|---:|---|---|---|---|
|0|`Shared0T.Insts.CoreConvertAsRef.as_ref`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op0_installed`|already-selected/no open op row|
|1|`Slice.Insts.CoreConvertAsRefSlice.as_ref`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op1_installed`|already-selected/no open op row|
|2|`core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op2_installed`|already-selected/no open op row|
|3|`core.mem.take`|True|OPEN; `None`|V169|
|4|`core.mem.drop`|True|OPEN; `None`|V170|
|5|`core.option.Option.is_some_and`|True|new source interpretation; `R1Z.PDict_RejectionStd.op5_installed`|already-selected/no open op row|
|6|`core.option.Option.as_ref`|True|new source interpretation; `R1Z.PDict_RejectionStd.op6_installed`|already-selected/no open op row|
|7|`core.option.Option.ok_or`|True|new source interpretation; `R1Z.PDict_RejectionStd.op7_installed`|already-selected/no open op row|
|8|`core.option.Option.Insts.CoreCmpPartialEqOption.eq`|True|new source interpretation; `R1Z.PDict_RejectionStd.op8_installed`|already-selected/no open op row|
|9|`core.option.Option.Insts.CoreOpsTry_traitTry.branch`|True|new source interpretation; `R1Z.PDict_RejectionStd.op9_installed`|already-selected/no open op row|
|10|`core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual`|True|new source interpretation; `R1Z.PDict_RejectionStd.op10_installed`|already-selected/no open op row|
|11|`core.result.Result.map`|True|new source interpretation; `R1Z.PDict_RejectionStd.op11_installed`|already-selected/no open op row|
|12|`core.result.Result.map_err`|True|inherited source interpretation; `None`|already-selected/no open op row|
|13|`core.sync.atomic.compiler_fence`|False|new source interpretation; `R1Z.PDict_ResumeDictionary.op13_installed`|already-selected/no open op row|
|14|`std.fs.File.open`|True|OPEN; `None`|V171|
|15|`std.fs.File.sync_all`|True|OPEN; `None`|V172|
|16|`std.io.Write.write_all.default`|False|OPEN; `None`|V173|
|17|`std.fs.File.Insts.StdIoWrite.flush`|False|new source interpretation; `R1Z.PDict_FileFlush.op17_installed`|already-selected/no open op row|
|18|`std.fs.File.Insts.StdIoWrite.write`|False|OPEN; `None`|V174|
|19|`std.fs.OpenOptions.new`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op19_installed`|already-selected/no open op row|
|20|`std.fs.OpenOptions.write`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op20_installed`|already-selected/no open op row|
|21|`std.fs.OpenOptions.create_new`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op21_installed`|already-selected/no open op row|
|22|`std.fs.OpenOptions.open`|True|OPEN; `None`|V175|
|23|`std.io.error.Error.kind`|True|OPEN; `None`|V176|
|24|`std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op24_installed`|already-selected/no open op row|
|25|`std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref`|True|OPEN; `None`|V177|
|26|`std.path.Path.join`|True|OPEN; `None`|V178|
|27|`std.path.Path.Insts.CoreConvertAsRefPath.as_ref`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op27_installed`|already-selected/no open op row|
|28|`alloc.string.String.Insts.CoreConvertAsRefPath.as_ref`|True|OPEN; `None`|V179|
|29|`std.path.PathBuf.Insts.CoreConvertAsRefPath.as_ref`|True|OPEN; `None`|V180|
|30|`alloc.string.String.with_capacity`|True|OPEN; `None`|V181|
|31|`alloc.string.String.push_str`|True|OPEN; `None`|V182|
|32|`alloc.vec.Vec.try_reserve_exact`|True|OPEN; `None`|V183|
|33|`alloc.vec.Vec.pop`|True|OPEN; `None`|V184|
|34|`alloc.vec.Vec.is_empty`|True|OPEN; `None`|V185|
|35|`alloc.vec.Vec.Insts.CoreDefaultDefault.default`|True|OPEN; `None`|V186|
|36|`Array.Insts.CoreConvertTryFromVecVec.try_from`|True|OPEN; `None`|V187|
|37|`aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq`|True|new source interpretation; `R1Z.PDict_PureDictionary.op37_installed`|V188|
|38|`aspis_core.digest.LegacyHashFn.Insts.CoreCloneClone.clone`|True|inherited source interpretation; `None`|already-selected/no open op row|
|39|`aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32.digest`|True|inherited source interpretation; `None`|already-selected/no open op row|
|40|`aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone.clone`|True|new source interpretation; `R1Z.PDict_PureDictionary.op40_installed`|V189|
|41|`aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq`|True|new source interpretation; `R1Z.PDict_PureDictionary.op41_installed`|V190|
|42|`aspis_core.field.wide_exact.WideExact.ZERO`|True|inherited source interpretation; `None`|already-selected/no open op row|
|43|`aspis_core.field.wide_exact.WideExact.impl.c0`|True|new source interpretation; `R1Z.PDict_PureDictionary.op43_installed`|V191|
|44|`aspis_core.field.wide_exact.WideExact.impl.c1`|True|new source interpretation; `R1Z.PDict_PureDictionary.op44_installed`|V192|
|45|`aspis_core.field.wide_exact.WideExact.from_qm31`|True|inherited source interpretation; `None`|already-selected/no open op row|
|46|`aspis_core.field.wide_exact.WideExact.add`|True|inherited source interpretation; `None`|already-selected/no open op row|
|47|`aspis_core.field.wide_exact.WideExact.mul`|True|inherited source interpretation; `None`|already-selected/no open op row|
|48|`aspis_core.field.wide_exact.WideExact.mul_qm31`|True|inherited source interpretation; `None`|already-selected/no open op row|
|49|`aspis_core.field.wide_exact.WideExact.to_limbs`|True|new source interpretation; `R1Z.PDict_CodecDictionary.op49_installed`|V193|
|50|`aspis_core.field.wide_exact.WideExact.from_le_bytes`|True|new source interpretation; `R1Z.PDict_CodecDictionary.op50_installed`|V194|
|51|`aspis_core.field.wide_exact.WideExact.to_le_bytes`|True|OPEN; `None`|V195|
|52|`aspis_core.field.wide_exact.WideExact.mul_m31`|True|inherited source interpretation; `None`|already-selected/no open op row|
|53|`aspis_core.field.M31.Insts.CoreCloneClone.clone`|True|inherited source interpretation; `None`|already-selected/no open op row|
|54|`aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq`|True|inherited source interpretation; `None`|already-selected/no open op row|
|55|`aspis_core.field.M31.ZERO`|True|inherited source interpretation; `None`|already-selected/no open op row|
|56|`aspis_core.field.M31.ONE`|True|inherited source interpretation; `None`|already-selected/no open op row|
|57|`aspis_core.field.M31.mul`|True|inherited source interpretation; `None`|already-selected/no open op row|
|58|`aspis_core.field.M31.double`|True|inherited source interpretation; `None`|already-selected/no open op row|
|59|`aspis_core.field.M31.inv`|True|inherited source interpretation; `None`|already-selected/no open op row|
|60|`aspis_core.field.CM31.new`|True|new source interpretation; `R1Z.PDict_PureDictionary.op60_installed`|V196|
|61|`aspis_core.field.CM31.from_m31`|True|inherited source interpretation; `None`|already-selected/no open op row|
|62|`aspis_core.field.QM31.Insts.CoreCloneClone.clone`|True|inherited source interpretation; `None`|already-selected/no open op row|
|63|`aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq`|True|inherited source interpretation; `None`|already-selected/no open op row|
|64|`aspis_core.field.QM31.ZERO`|True|inherited source interpretation; `None`|already-selected/no open op row|
|65|`aspis_core.field.QM31.ONE`|True|inherited source interpretation; `None`|already-selected/no open op row|
|66|`aspis_core.field.QM31.from_cm31`|True|inherited source interpretation; `None`|already-selected/no open op row|
|67|`aspis_core.field.QM31.add`|True|inherited source interpretation; `None`|already-selected/no open op row|
|68|`aspis_core.field.QM31.sub`|True|inherited source interpretation; `None`|already-selected/no open op row|
|69|`aspis_core.field.QM31.mul`|True|inherited source interpretation; `None`|already-selected/no open op row|
|70|`aspis_core.field.QM31.mul_m31`|True|inherited source interpretation; `None`|already-selected/no open op row|
|71|`aspis_core.field.QM31.from_le_bytes`|True|OPEN; `None`|V197|
|72|`aspis_core.field.QM31.write_le_bytes`|True|OPEN; `None`|V198|
|73|`aspis_core.field.M31.add`|True|inherited source interpretation; `None`|already-selected/no open op row|
|74|`aspis_core.field.M31.sub`|True|inherited source interpretation; `None`|already-selected/no open op row|
|75|`aspis_core.r0.domain.FibreIndex.new`|True|inherited source interpretation; `None`|already-selected/no open op row|
|76|`aspis_core.r0.domain.FibreIndex.get`|True|inherited source interpretation; `None`|already-selected/no open op row|
|77|`aspis_core.r0.domain.Point.Insts.CoreCloneClone.clone`|True|OPEN; `None`|V199|
|78|`aspis_core.r0.domain.fibre_point`|True|OPEN; `None`|V200|
|79|`aspis_core.r0.encoder.eval_message`|True|OPEN; `None`|V201|
|80|`aspis_core.r0.fold.phi_inverse`|True|OPEN; `None`|V202|
|81|`aspis_core.r0.heap.filled`|True|OPEN; `None`|V203|
|82|`aspis_core.r0.merkle.C1_TAG`|True|OPEN; `None`|V204|
|83|`aspis_core.r0.merkle.C2_TAG`|True|OPEN; `None`|V205|
|84|`aspis_core.r0.merkle.leaf`|True|OPEN; `None`|V206|
|85|`aspis_core.r0.Error.Insts.CoreFmtDebug.fmt`|False|OPEN; `None`|V207|
|86|`aspis_core.r0.opening.LANES`|True|OPEN; `None`|V208|
|87|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.ZERO`|True|inherited source interpretation; `None`|already-selected/no open op row|
|88|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.ZERO`|True|inherited source interpretation; `None`|already-selected/no open op row|
|89|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.ZERO`|True|inherited source interpretation; `None`|already-selected/no open op row|
|90|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.ONE`|True|inherited source interpretation; `None`|already-selected/no open op row|
|91|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.ONE`|True|inherited source interpretation; `None`|already-selected/no open op row|
|92|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.ONE`|True|inherited source interpretation; `None`|already-selected/no open op row|
|93|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.add`|True|inherited source interpretation; `None`|already-selected/no open op row|
|94|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.add`|True|inherited source interpretation; `None`|already-selected/no open op row|
|95|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.add`|True|inherited source interpretation; `None`|already-selected/no open op row|
|96|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.sub`|True|inherited source interpretation; `None`|already-selected/no open op row|
|97|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.sub`|True|inherited source interpretation; `None`|already-selected/no open op row|
|98|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.sub`|True|inherited source interpretation; `None`|already-selected/no open op row|
|99|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.neg`|True|inherited source interpretation; `None`|already-selected/no open op row|
|100|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.neg`|True|OPEN; `None`|V209|
|101|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.neg`|True|OPEN; `None`|V210|
|102|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.mul`|True|inherited source interpretation; `None`|already-selected/no open op row|
|103|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.mul`|True|inherited source interpretation; `None`|already-selected/no open op row|
|104|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.mul`|True|inherited source interpretation; `None`|already-selected/no open op row|
|105|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv`|True|OPEN; `None`|V211|
|106|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.from_m31`|True|inherited source interpretation; `None`|already-selected/no open op row|
|107|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.try_inv`|True|OPEN; `None`|V212|
|108|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.from_m31`|True|inherited source interpretation; `None`|already-selected/no open op row|
|109|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.try_inv`|True|OPEN; `None`|V213|
|110|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31`|True|OPEN; `None`|V214|
|111|`aspis_core.state_only_hiding.PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT`|True|OPEN; `None`|V215|
|112|`aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1`|True|inherited source interpretation; `None`|already-selected/no open op row|
|113|`aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1`|True|inherited source interpretation; `None`|already-selected/no open op row|
|114|`aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext.eq`|True|OPEN; `None`|V216|
|115|`aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1`|True|inherited source interpretation; `None`|already-selected/no open op row|
|116|`aspis_core.state_only_hiding.StateOnlyHidingContext.encode`|True|inherited source interpretation; `None`|already-selected/no open op row|
|117|`aspis_core.state_only_hiding.state_only_selected_mask_value`|True|OPEN; `None`|V217|
|118|`aspis_core.state_only_prefix.r0.statement_points`|True|OPEN; `None`|V218|
|119|`aspis_core.state_only_private_merkle.private_leaf_hash`|True|inherited source interpretation; `None`|already-selected/no open op row|
|120|`aspis_core.state_only_sumcheck.state_only_boundary_sum`|True|OPEN; `None`|V219|
|121|`aspis_core.state_only_sumcheck.evaluate_state_only_polynomial`|True|OPEN; `None`|V220|
|122|`Array.Insts.ZeroizeZeroize.zeroize`|True|OPEN; `None`|V221|
|123|`zeroize.Zeroize.Blanket.zeroize`|True|OPEN; `None`|V222|
|124|`aspis_prover.state_only_hiding.volatile_clear_cell`|False|new source interpretation; `R1Z.PDict_VolatileCell.op124_installed`|already-selected/no open op row|
|125|`zeroize.Zeroizing.Insts.CoreConvertAsMut.as_mut`|True|new source interpretation; `R1Z.PDict_OffpathBorrow.op125_installed`|already-selected/no open op row|
|126|`zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut`|True|new source interpretation; `R1Z.PDict_OffpathBorrow.op126_installed`|already-selected/no open op row|
|127|`zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref`|True|OPEN; `None`|V223|
|128|`zeroize.Zeroizing.new`|True|OPEN; `None`|V224|
|129|`getrandom.fill`|True|OPEN; `None`|V225|
|130|`zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize`|True|OPEN; `None`|V226|
|131|`zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref`|True|OPEN; `None`|V227|
|132|`aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1`|True|OPEN; `None`|V228|
|133|`aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_rows_v1`|True|OPEN; `None`|V229|
|134|`aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1`|True|OPEN; `None`|V230|
|135|`typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUTermSoFarSoFar.private_cmp`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op135_installed`|already-selected/no open op row|
|136|`typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUIntSoFarLess.private_cmp`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op136_installed`|already-selected/no open op row|
|137|`typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB0SoFarClause3_Output.private_cmp`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op137_installed`|already-selected/no open op row|
|138|`typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB1SoFarClause3_Output.private_cmp`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op138_installed`|already-selected/no open op row|
|139|`typenum.uint.UIntUlB0.Insts.TypenumPrivatePrivateCmpUIntUrB0SoFarClause3_Output.private_cmp`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op139_installed`|already-selected/no open op row|
|140|`typenum.uint.UIntUlB0.Insts.TypenumType_operatorsCmpUIntUrB0Clause2_Output.compare`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op140_installed`|already-selected/no open op row|
|141|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_isize`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op141_installed`|already-selected/no open op row|
|142|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i64`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op142_installed`|already-selected/no open op row|
|143|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i32`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op143_installed`|already-selected/no open op row|
|144|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i16`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op144_installed`|already-selected/no open op row|
|145|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i8`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op145_installed`|already-selected/no open op row|
|146|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_usize`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op146_installed`|already-selected/no open op row|
|147|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u64`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op147_installed`|already-selected/no open op row|
|148|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u32`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op148_installed`|already-selected/no open op row|
|149|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u16`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op149_installed`|already-selected/no open op row|
|150|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u8`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op150_installed`|already-selected/no open op row|
|151|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.ISIZE`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op151_installed`|already-selected/no open op row|
|152|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I64`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op152_installed`|already-selected/no open op row|
|153|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I32`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op153_installed`|already-selected/no open op row|
|154|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I16`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op154_installed`|already-selected/no open op row|
|155|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I8`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op155_installed`|already-selected/no open op row|
|156|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.USIZE`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op156_installed`|already-selected/no open op row|
|157|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U64`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op157_installed`|already-selected/no open op row|
|158|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U32`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op158_installed`|already-selected/no open op row|
|159|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U16`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op159_installed`|already-selected/no open op row|
|160|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U8`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op160_installed`|already-selected/no open op row|
|161|`typenum.uint.UInt.Insts.CoreDefaultDefault.default`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op161_installed`|already-selected/no open op row|
|162|`typenum.uint.UInt.Insts.CoreCloneClone.clone`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op162_installed`|already-selected/no open op row|
|163|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_isize`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op163_installed`|already-selected/no open op row|
|164|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i64`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op164_installed`|already-selected/no open op row|
|165|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i32`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op165_installed`|already-selected/no open op row|
|166|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i16`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op166_installed`|already-selected/no open op row|
|167|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i8`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op167_installed`|already-selected/no open op row|
|168|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_usize`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op168_installed`|already-selected/no open op row|
|169|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u64`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op169_installed`|already-selected/no open op row|
|170|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u32`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op170_installed`|already-selected/no open op row|
|171|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u16`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op171_installed`|already-selected/no open op row|
|172|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u8`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op172_installed`|already-selected/no open op row|
|173|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.ISIZE`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op173_installed`|already-selected/no open op row|
|174|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I64`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op174_installed`|already-selected/no open op row|
|175|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I32`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op175_installed`|already-selected/no open op row|
|176|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I16`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op176_installed`|already-selected/no open op row|
|177|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I8`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op177_installed`|already-selected/no open op row|
|178|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.USIZE`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op178_installed`|already-selected/no open op row|
|179|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U64`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op179_installed`|already-selected/no open op row|
|180|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U32`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op180_installed`|already-selected/no open op row|
|181|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U16`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op181_installed`|already-selected/no open op row|
|182|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U8`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op182_installed`|already-selected/no open op row|
|183|`typenum.uint.UTerm.Insts.CoreDefaultDefault.default`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op183_installed`|already-selected/no open op row|
|184|`typenum.uint.UTerm.Insts.CoreCloneClone.clone`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op184_installed`|already-selected/no open op row|
|185|`typenum.type_operators.IsLessOrEqual.Blanket.is_less_or_equal`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op185_installed`|already-selected/no open op row|
|186|`typenum.type_operators.IsLess.Blanket.is_less`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op186_installed`|already-selected/no open op row|
|187|`typenum.private.IsLessOrEqualPrivateABEqualB1.Blanket.is_less_or_equal_private`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op187_installed`|already-selected/no open op row|
|188|`typenum.bit.B1.Insts.TypenumMarker_traitsBit.to_bool`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op188_installed`|already-selected/no open op row|
|189|`typenum.bit.B1.Insts.TypenumMarker_traitsBit.to_u8`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op189_installed`|already-selected/no open op row|
|190|`typenum.bit.B1.Insts.TypenumMarker_traitsBit.new`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op190_installed`|already-selected/no open op row|
|191|`typenum.bit.B1.Insts.TypenumMarker_traitsBit.BOOL`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op191_installed`|already-selected/no open op row|
|192|`typenum.bit.B1.Insts.TypenumMarker_traitsBit.U8`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op192_installed`|already-selected/no open op row|
|193|`typenum.bit.B1.Insts.CoreDefaultDefault.default`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op193_installed`|already-selected/no open op row|
|194|`typenum.bit.B1.Insts.CoreCloneClone.clone`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op194_installed`|already-selected/no open op row|
|195|`typenum.private.IsLessPrivateABLessB1.Blanket.is_less_private`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op195_installed`|already-selected/no open op row|
|196|`typenum.Equal.Insts.TypenumMarker_traitsOrd.to_ordering`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op196_installed`|already-selected/no open op row|
|197|`typenum.Greater.Insts.TypenumMarker_traitsOrd.to_ordering`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op197_installed`|already-selected/no open op row|
|198|`typenum.bit.B0.Insts.TypenumMarker_traitsBit.to_bool`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op198_installed`|already-selected/no open op row|
|199|`typenum.bit.B0.Insts.TypenumMarker_traitsBit.to_u8`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op199_installed`|already-selected/no open op row|
|200|`typenum.bit.B0.Insts.TypenumMarker_traitsBit.new`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op200_installed`|already-selected/no open op row|
|201|`typenum.bit.B0.Insts.TypenumMarker_traitsBit.BOOL`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op201_installed`|already-selected/no open op row|
|202|`typenum.bit.B0.Insts.TypenumMarker_traitsBit.U8`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op202_installed`|already-selected/no open op row|
|203|`typenum.bit.B0.Insts.CoreDefaultDefault.default`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op203_installed`|already-selected/no open op row|
|204|`typenum.bit.B0.Insts.CoreCloneClone.clone`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op204_installed`|already-selected/no open op row|
|205|`sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.finalize_variable_core`|True|OPEN; `None`|V231|
|206|`sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.new`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op206_installed`|already-selected/no open op row|
|207|`sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.TRUNC_SIDE`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op207_installed`|already-selected/no open op row|
|208|`sha2.core_api.Sha256VarCore.Insts.DigestCore_apiUpdateCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80.update_blocks`|True|OPEN; `None`|V232|
|209|`block_buffer.Eager.Insts.Block_bufferSealedSealed.split_blocks`|True|OPEN; `None`|V233|
|210|`block_buffer.Eager.Insts.Block_bufferSealedSealed.invariant`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op210_installed`|already-selected/no open op row|
|211|`ArrayT32.Insts.CoreConvertFromGenericArrayTUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplOddTArrayT0.from`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op211_installed`|already-selected/no open op row|
|212|`digest.digest.Digest.Blanket.finalize`|True|OPEN; `None`|V234|
|213|`digest.digest.Digest.Blanket.update`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op213_installed`|already-selected/no open op row|
|214|`digest.digest.Digest.Blanket.new`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op214_installed`|already-selected/no open op row|
|215|`digest.core_api.wrapper.CoreWrapper.Insts.DigestFixedOutput.finalize_into`|True|OPEN; `None`|V235|
|216|`digest.core_api.wrapper.CoreWrapper.Insts.DigestUpdate.update`|True|OPEN; `None`|V236|
|217|`digest.core_api.wrapper.CoreWrapper.Insts.CoreDefaultDefault.default`|True|OPEN; `None`|V237|
|218|`digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.CoreDefaultDefault.default`|True|new source interpretation; `R1Z.PDict_CtConstructor.op218_installed`|already-selected/no open op row|
|219|`digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.DigestCore_apiFixedOutputCore.finalize_fixed_core`|True|OPEN; `None`|V238|
|220|`digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.DigestCore_apiUpdateCore.update_blocks`|True|new source interpretation; `R1Z.PDict_CtUpdate.op220_installed`|already-selected/no open op row|
|221|`block_buffer.Eager.Insts.CoreDefaultDefault.default`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op221_installed`|already-selected/no open op row|
|222|`aspis_statement.constraints_v4.multilinear_evaluate_qm31`|True|OPEN; `None`|V239|
|223|`aspis_statement.logup.compress_tagged_tuple`|True|OPEN; `None`|V240|
|224|`aspis_statement.pool_v1.pair_forest_semantic_oracle.build_pool_v1_pair_forest_copy_helper_v1`|True|OPEN; `None`|V241|
|225|`aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.transition`|True|OPEN; `None`|V242|
|226|`aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes`|True|OPEN; `None`|V243|
|227|`aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31`|True|OPEN; `None`|V244|
|228|`aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1`|True|OPEN; `None`|V245|
|229|`aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1.eq`|True|OPEN; `None`|V246|
|230|`aspis_statement.state_only_semantic.state_only_copy_helper_sum`|True|OPEN; `None`|V247|
|231|`aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone`|True|OPEN; `None`|V248|
|232|`aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.p_r1_check`|True|OPEN; `None`|V249|
|233|`transport.Variant.Insts.CoreCmpPartialEqVariant.eq`|True|inherited source interpretation; `None`|already-selected/no open op row|
|234|`transport.Variant.tag`|True|inherited source interpretation; `None`|already-selected/no open op row|
|235|`multiproof.LEAF_BITS`|True|new source interpretation; `R1Z.PDict_PureDictionary.op235_installed`|V250|
|236|`multiproof.MAX_BATCH`|True|new source interpretation; `R1Z.PDict_PureDictionary.op236_installed`|V251|
|237|`compact.SLOT_NODES`|True|inherited source interpretation; `None`|already-selected/no open op row|
|238|`host_commitment.clear_private_salt`|False|new source interpretation; `R1Z.PDict_ResumeDictionary.op238_installed`|already-selected/no open op row|
|239|`r1_wire.CLAIMS`|True|new source interpretation; `R1Z.PDict_PureDictionary.op239_installed`|V252|
|240|`r1_wire.LANES`|True|new source interpretation; `R1Z.PDict_PureDictionary.op240_installed`|V253|
|241|`compact.LOGICAL_SEMANTIC`|True|inherited source interpretation; `None`|already-selected/no open op row|
|242|`compact.PROOF_BYTES`|True|inherited source interpretation; `None`|already-selected/no open op row|
|243|`compact.OFF_NODES`|True|inherited source interpretation; `None`|already-selected/no open op row|
|244|`compact.OFF_OPENINGS`|True|inherited source interpretation; `None`|already-selected/no open op row|
|245|`compact.MAGIC`|True|inherited source interpretation; `None`|already-selected/no open op row|
|246|`multiproof.binary_parent`|True|OPEN; `None`|V254|
|247|`trace.value`|True|OPEN; `None`|V255|
|248|`sampler.qm31_sample`|True|inherited source interpretation; `None`|already-selected/no open op row|
|249|`sampler.gamma_sample`|True|OPEN; `None`|V256|
|250|`sampler.ordinary_sample`|True|OPEN; `None`|V257|
|251|`weights.Weights.materialize`|True|OPEN; `None`|V258|
|252|`weights.Weights.new`|True|OPEN; `None`|V259|
|253|`weights.Weights.raw`|True|OPEN; `None`|V260|
|254|`weights.powers`|True|OPEN; `None`|V261|
|255|`transport.Variant.coefficients`|True|OPEN; `None`|V262|
|256|`r1_wire.Error.Insts.CoreCmpPartialEqError.eq`|True|new source interpretation; `R1Z.PDict_ResumeDictionary.op256_installed`|already-selected/no open op row|
|257|`host_work.map`|True|OPEN; `None`|V263|
|258|`ct_pole.all_slots_clear`|True|OPEN; `None`|V264|
|259|`sampler.circle_sample`|True|OPEN; `None`|V265|
|260|`r1_wire.DOMAIN`|True|new source interpretation; `R1Z.PDict_PureDictionary.op260_installed`|V266|
|261|`std.fs.File.Insts.StdIoWrite.write_all`|True|OPEN; `None`|V267|
