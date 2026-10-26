# Installed prover dictionary and current source requirement

Target not yet established. **172 selected /83 open /255 sufficient required source fields**. Historical full dictionary:176 selected /86 open /262. Seven field irrelevances remove four selected and three open fields. Positive feasible-native-invocation counts remain unestablished. Native type-value associations:26/28;3 IOError and27 Formatter remain open. Root premises removed:0.

| ID | Name | Required by source bound | Selection / theorem |
|---:|---|---|---|
|0|`Shared0T.Insts.CoreConvertAsRef.as_ref`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op0_installed`|
|1|`Slice.Insts.CoreConvertAsRefSlice.as_ref`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op1_installed`|
|2|`core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op2_installed`|
|3|`core.mem.take`|yes|OPEN; `OPEN`|
|4|`core.mem.drop`|yes|OPEN; `OPEN`|
|5|`core.option.Option.is_some_and`|yes|new source interpretation; `R1Z.PDict_RejectionStd.op5_installed`|
|6|`core.option.Option.as_ref`|yes|new source interpretation; `R1Z.PDict_RejectionStd.op6_installed`|
|7|`core.option.Option.ok_or`|yes|new source interpretation; `R1Z.PDict_RejectionStd.op7_installed`|
|8|`core.option.Option.Insts.CoreCmpPartialEqOption.eq`|yes|new source interpretation; `R1Z.PDict_RejectionStd.op8_installed`|
|9|`core.option.Option.Insts.CoreOpsTry_traitTry.branch`|yes|new source interpretation; `R1Z.PDict_RejectionStd.op9_installed`|
|10|`core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual`|yes|new source interpretation; `R1Z.PDict_RejectionStd.op10_installed`|
|11|`core.result.Result.map`|yes|new source interpretation; `R1Z.PDict_RejectionStd.op11_installed`|
|12|`core.result.Result.map_err`|yes|inherited source interpretation; `inherited selection`|
|13|`core.sync.atomic.compiler_fence`|no|new source interpretation; `R1Z.PDict_ResumeDictionary.op13_installed`; `R1Z.PDict_ReachCaller.op13_irrelevant`|
|14|`std.fs.File.open`|yes|OPEN; `OPEN`|
|15|`std.fs.File.sync_all`|yes|OPEN; `OPEN`|
|16|`std.io.Write.write_all.default`|no|OPEN; `OPEN`; `R1Z.PDict_ReachCaller.op16_irrelevant`|
|17|`std.fs.File.Insts.StdIoWrite.flush`|no|new source interpretation; `R1Z.PDict_FileFlush.op17_installed`; `R1Z.PDict_ReachCaller.op17_irrelevant`|
|18|`std.fs.File.Insts.StdIoWrite.write`|no|OPEN; `OPEN`; `R1Z.PDict_ReachCaller.op18_irrelevant`|
|19|`std.fs.OpenOptions.new`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op19_installed`|
|20|`std.fs.OpenOptions.write`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op20_installed`|
|21|`std.fs.OpenOptions.create_new`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op21_installed`|
|22|`std.fs.OpenOptions.open`|yes|OPEN; `OPEN`|
|23|`std.io.error.Error.kind`|yes|OPEN; `OPEN`|
|24|`std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op24_installed`|
|25|`std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref`|yes|OPEN; `OPEN`|
|26|`std.path.Path.join`|yes|OPEN; `OPEN`|
|27|`std.path.Path.Insts.CoreConvertAsRefPath.as_ref`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op27_installed`|
|28|`alloc.string.String.Insts.CoreConvertAsRefPath.as_ref`|yes|OPEN; `OPEN`|
|29|`std.path.PathBuf.Insts.CoreConvertAsRefPath.as_ref`|yes|OPEN; `OPEN`|
|30|`alloc.string.String.with_capacity`|yes|OPEN; `OPEN`|
|31|`alloc.string.String.push_str`|yes|OPEN; `OPEN`|
|32|`alloc.vec.Vec.try_reserve_exact`|yes|OPEN; `OPEN`|
|33|`alloc.vec.Vec.pop`|yes|OPEN; `OPEN`|
|34|`alloc.vec.Vec.is_empty`|yes|OPEN; `OPEN`|
|35|`alloc.vec.Vec.Insts.CoreDefaultDefault.default`|yes|OPEN; `OPEN`|
|36|`Array.Insts.CoreConvertTryFromVecVec.try_from`|yes|OPEN; `OPEN`|
|37|`aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq`|yes|new source interpretation; `R1Z.PDict_PureDictionary.op37_installed`|
|38|`aspis_core.digest.LegacyHashFn.Insts.CoreCloneClone.clone`|yes|inherited source interpretation; `inherited selection`|
|39|`aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32.digest`|yes|inherited source interpretation; `inherited selection`|
|40|`aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone.clone`|yes|new source interpretation; `R1Z.PDict_PureDictionary.op40_installed`|
|41|`aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq`|yes|new source interpretation; `R1Z.PDict_PureDictionary.op41_installed`|
|42|`aspis_core.field.wide_exact.WideExact.ZERO`|yes|inherited source interpretation; `inherited selection`|
|43|`aspis_core.field.wide_exact.WideExact.impl.c0`|yes|new source interpretation; `R1Z.PDict_PureDictionary.op43_installed`|
|44|`aspis_core.field.wide_exact.WideExact.impl.c1`|yes|new source interpretation; `R1Z.PDict_PureDictionary.op44_installed`|
|45|`aspis_core.field.wide_exact.WideExact.from_qm31`|yes|inherited source interpretation; `inherited selection`|
|46|`aspis_core.field.wide_exact.WideExact.add`|yes|inherited source interpretation; `inherited selection`|
|47|`aspis_core.field.wide_exact.WideExact.mul`|yes|inherited source interpretation; `inherited selection`|
|48|`aspis_core.field.wide_exact.WideExact.mul_qm31`|yes|inherited source interpretation; `inherited selection`|
|49|`aspis_core.field.wide_exact.WideExact.to_limbs`|yes|new source interpretation; `R1Z.PDict_CodecDictionary.op49_installed`|
|50|`aspis_core.field.wide_exact.WideExact.from_le_bytes`|yes|new source interpretation; `R1Z.PDict_CodecDictionary.op50_installed`|
|51|`aspis_core.field.wide_exact.WideExact.to_le_bytes`|yes|OPEN; `OPEN`|
|52|`aspis_core.field.wide_exact.WideExact.mul_m31`|yes|inherited source interpretation; `inherited selection`|
|53|`aspis_core.field.M31.Insts.CoreCloneClone.clone`|yes|inherited source interpretation; `inherited selection`|
|54|`aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq`|yes|inherited source interpretation; `inherited selection`|
|55|`aspis_core.field.M31.ZERO`|yes|inherited source interpretation; `inherited selection`|
|56|`aspis_core.field.M31.ONE`|yes|inherited source interpretation; `inherited selection`|
|57|`aspis_core.field.M31.mul`|yes|inherited source interpretation; `inherited selection`|
|58|`aspis_core.field.M31.double`|yes|inherited source interpretation; `inherited selection`|
|59|`aspis_core.field.M31.inv`|yes|inherited source interpretation; `inherited selection`|
|60|`aspis_core.field.CM31.new`|yes|new source interpretation; `R1Z.PDict_PureDictionary.op60_installed`|
|61|`aspis_core.field.CM31.from_m31`|yes|inherited source interpretation; `inherited selection`|
|62|`aspis_core.field.QM31.Insts.CoreCloneClone.clone`|yes|inherited source interpretation; `inherited selection`|
|63|`aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq`|yes|inherited source interpretation; `inherited selection`|
|64|`aspis_core.field.QM31.ZERO`|yes|inherited source interpretation; `inherited selection`|
|65|`aspis_core.field.QM31.ONE`|yes|inherited source interpretation; `inherited selection`|
|66|`aspis_core.field.QM31.from_cm31`|yes|inherited source interpretation; `inherited selection`|
|67|`aspis_core.field.QM31.add`|yes|inherited source interpretation; `inherited selection`|
|68|`aspis_core.field.QM31.sub`|yes|inherited source interpretation; `inherited selection`|
|69|`aspis_core.field.QM31.mul`|yes|inherited source interpretation; `inherited selection`|
|70|`aspis_core.field.QM31.mul_m31`|yes|inherited source interpretation; `inherited selection`|
|71|`aspis_core.field.QM31.from_le_bytes`|yes|OPEN; `OPEN`|
|72|`aspis_core.field.QM31.write_le_bytes`|yes|OPEN; `OPEN`|
|73|`aspis_core.field.M31.add`|yes|inherited source interpretation; `inherited selection`|
|74|`aspis_core.field.M31.sub`|yes|inherited source interpretation; `inherited selection`|
|75|`aspis_core.r0.domain.FibreIndex.new`|yes|inherited source interpretation; `inherited selection`|
|76|`aspis_core.r0.domain.FibreIndex.get`|yes|inherited source interpretation; `inherited selection`|
|77|`aspis_core.r0.domain.Point.Insts.CoreCloneClone.clone`|yes|OPEN; `OPEN`|
|78|`aspis_core.r0.domain.fibre_point`|yes|OPEN; `OPEN`|
|79|`aspis_core.r0.encoder.eval_message`|yes|OPEN; `OPEN`|
|80|`aspis_core.r0.fold.phi_inverse`|yes|OPEN; `OPEN`|
|81|`aspis_core.r0.heap.filled`|yes|OPEN; `OPEN`|
|82|`aspis_core.r0.merkle.C1_TAG`|yes|OPEN; `OPEN`|
|83|`aspis_core.r0.merkle.C2_TAG`|yes|OPEN; `OPEN`|
|84|`aspis_core.r0.merkle.leaf`|yes|OPEN; `OPEN`|
|85|`aspis_core.r0.Error.Insts.CoreFmtDebug.fmt`|no|OPEN; `OPEN`; `R1Z.PDict_ReachCaller.op85_irrelevant`|
|86|`aspis_core.r0.opening.LANES`|yes|OPEN; `OPEN`|
|87|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.ZERO`|yes|inherited source interpretation; `inherited selection`|
|88|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.ZERO`|yes|inherited source interpretation; `inherited selection`|
|89|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.ZERO`|yes|inherited source interpretation; `inherited selection`|
|90|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.ONE`|yes|inherited source interpretation; `inherited selection`|
|91|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.ONE`|yes|inherited source interpretation; `inherited selection`|
|92|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.ONE`|yes|inherited source interpretation; `inherited selection`|
|93|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.add`|yes|inherited source interpretation; `inherited selection`|
|94|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.add`|yes|inherited source interpretation; `inherited selection`|
|95|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.add`|yes|inherited source interpretation; `inherited selection`|
|96|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.sub`|yes|inherited source interpretation; `inherited selection`|
|97|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.sub`|yes|inherited source interpretation; `inherited selection`|
|98|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.sub`|yes|inherited source interpretation; `inherited selection`|
|99|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.neg`|yes|inherited source interpretation; `inherited selection`|
|100|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.neg`|yes|OPEN; `OPEN`|
|101|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.neg`|yes|OPEN; `OPEN`|
|102|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.mul`|yes|inherited source interpretation; `inherited selection`|
|103|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.mul`|yes|inherited source interpretation; `inherited selection`|
|104|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.mul`|yes|inherited source interpretation; `inherited selection`|
|105|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv`|yes|OPEN; `OPEN`|
|106|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.from_m31`|yes|inherited source interpretation; `inherited selection`|
|107|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.try_inv`|yes|OPEN; `OPEN`|
|108|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.from_m31`|yes|inherited source interpretation; `inherited selection`|
|109|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.try_inv`|yes|OPEN; `OPEN`|
|110|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31`|yes|OPEN; `OPEN`|
|111|`aspis_core.state_only_hiding.PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT`|yes|OPEN; `OPEN`|
|112|`aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1`|yes|inherited source interpretation; `inherited selection`|
|113|`aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1`|yes|inherited source interpretation; `inherited selection`|
|114|`aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext.eq`|yes|OPEN; `OPEN`|
|115|`aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1`|yes|inherited source interpretation; `inherited selection`|
|116|`aspis_core.state_only_hiding.StateOnlyHidingContext.encode`|yes|inherited source interpretation; `inherited selection`|
|117|`aspis_core.state_only_hiding.state_only_selected_mask_value`|yes|OPEN; `OPEN`|
|118|`aspis_core.state_only_prefix.r0.statement_points`|yes|OPEN; `OPEN`|
|119|`aspis_core.state_only_private_merkle.private_leaf_hash`|yes|inherited source interpretation; `inherited selection`|
|120|`aspis_core.state_only_sumcheck.state_only_boundary_sum`|yes|OPEN; `OPEN`|
|121|`aspis_core.state_only_sumcheck.evaluate_state_only_polynomial`|yes|OPEN; `OPEN`|
|122|`Array.Insts.ZeroizeZeroize.zeroize`|yes|OPEN; `OPEN`|
|123|`zeroize.Zeroize.Blanket.zeroize`|yes|OPEN; `OPEN`|
|124|`aspis_prover.state_only_hiding.volatile_clear_cell`|no|new source interpretation; `R1Z.PDict_VolatileCell.op124_installed`; `R1Z.PDict_ReachCaller.op124_irrelevant`|
|125|`zeroize.Zeroizing.Insts.CoreConvertAsMut.as_mut`|yes|new source interpretation; `R1Z.PDict_OffpathBorrow.op125_installed`|
|126|`zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut`|yes|new source interpretation; `R1Z.PDict_OffpathBorrow.op126_installed`|
|127|`zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref`|yes|OPEN; `OPEN`|
|128|`zeroize.Zeroizing.new`|yes|OPEN; `OPEN`|
|129|`getrandom.fill`|yes|OPEN; `OPEN`|
|130|`zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize`|yes|OPEN; `OPEN`|
|131|`zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref`|yes|OPEN; `OPEN`|
|132|`aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1`|yes|OPEN; `OPEN`|
|133|`aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_rows_v1`|yes|OPEN; `OPEN`|
|134|`aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1`|yes|OPEN; `OPEN`|
|135|`typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUTermSoFarSoFar.private_cmp`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op135_installed`|
|136|`typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUIntSoFarLess.private_cmp`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op136_installed`|
|137|`typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB0SoFarClause3_Output.private_cmp`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op137_installed`|
|138|`typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB1SoFarClause3_Output.private_cmp`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op138_installed`|
|139|`typenum.uint.UIntUlB0.Insts.TypenumPrivatePrivateCmpUIntUrB0SoFarClause3_Output.private_cmp`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op139_installed`|
|140|`typenum.uint.UIntUlB0.Insts.TypenumType_operatorsCmpUIntUrB0Clause2_Output.compare`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op140_installed`|
|141|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_isize`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op141_installed`|
|142|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i64`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op142_installed`|
|143|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i32`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op143_installed`|
|144|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i16`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op144_installed`|
|145|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i8`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op145_installed`|
|146|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_usize`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op146_installed`|
|147|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u64`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op147_installed`|
|148|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u32`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op148_installed`|
|149|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u16`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op149_installed`|
|150|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u8`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op150_installed`|
|151|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.ISIZE`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op151_installed`|
|152|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I64`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op152_installed`|
|153|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I32`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op153_installed`|
|154|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I16`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op154_installed`|
|155|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I8`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op155_installed`|
|156|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.USIZE`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op156_installed`|
|157|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U64`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op157_installed`|
|158|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U32`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op158_installed`|
|159|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U16`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op159_installed`|
|160|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U8`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op160_installed`|
|161|`typenum.uint.UInt.Insts.CoreDefaultDefault.default`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op161_installed`|
|162|`typenum.uint.UInt.Insts.CoreCloneClone.clone`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op162_installed`|
|163|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_isize`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op163_installed`|
|164|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i64`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op164_installed`|
|165|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i32`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op165_installed`|
|166|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i16`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op166_installed`|
|167|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i8`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op167_installed`|
|168|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_usize`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op168_installed`|
|169|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u64`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op169_installed`|
|170|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u32`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op170_installed`|
|171|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u16`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op171_installed`|
|172|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u8`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op172_installed`|
|173|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.ISIZE`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op173_installed`|
|174|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I64`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op174_installed`|
|175|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I32`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op175_installed`|
|176|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I16`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op176_installed`|
|177|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I8`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op177_installed`|
|178|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.USIZE`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op178_installed`|
|179|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U64`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op179_installed`|
|180|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U32`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op180_installed`|
|181|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U16`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op181_installed`|
|182|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U8`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op182_installed`|
|183|`typenum.uint.UTerm.Insts.CoreDefaultDefault.default`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op183_installed`|
|184|`typenum.uint.UTerm.Insts.CoreCloneClone.clone`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op184_installed`|
|185|`typenum.type_operators.IsLessOrEqual.Blanket.is_less_or_equal`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op185_installed`|
|186|`typenum.type_operators.IsLess.Blanket.is_less`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op186_installed`|
|187|`typenum.private.IsLessOrEqualPrivateABEqualB1.Blanket.is_less_or_equal_private`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op187_installed`|
|188|`typenum.bit.B1.Insts.TypenumMarker_traitsBit.to_bool`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op188_installed`|
|189|`typenum.bit.B1.Insts.TypenumMarker_traitsBit.to_u8`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op189_installed`|
|190|`typenum.bit.B1.Insts.TypenumMarker_traitsBit.new`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op190_installed`|
|191|`typenum.bit.B1.Insts.TypenumMarker_traitsBit.BOOL`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op191_installed`|
|192|`typenum.bit.B1.Insts.TypenumMarker_traitsBit.U8`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op192_installed`|
|193|`typenum.bit.B1.Insts.CoreDefaultDefault.default`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op193_installed`|
|194|`typenum.bit.B1.Insts.CoreCloneClone.clone`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op194_installed`|
|195|`typenum.private.IsLessPrivateABLessB1.Blanket.is_less_private`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op195_installed`|
|196|`typenum.Equal.Insts.TypenumMarker_traitsOrd.to_ordering`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op196_installed`|
|197|`typenum.Greater.Insts.TypenumMarker_traitsOrd.to_ordering`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op197_installed`|
|198|`typenum.bit.B0.Insts.TypenumMarker_traitsBit.to_bool`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op198_installed`|
|199|`typenum.bit.B0.Insts.TypenumMarker_traitsBit.to_u8`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op199_installed`|
|200|`typenum.bit.B0.Insts.TypenumMarker_traitsBit.new`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op200_installed`|
|201|`typenum.bit.B0.Insts.TypenumMarker_traitsBit.BOOL`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op201_installed`|
|202|`typenum.bit.B0.Insts.TypenumMarker_traitsBit.U8`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op202_installed`|
|203|`typenum.bit.B0.Insts.CoreDefaultDefault.default`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op203_installed`|
|204|`typenum.bit.B0.Insts.CoreCloneClone.clone`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op204_installed`|
|205|`sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.finalize_variable_core`|yes|OPEN; `OPEN`|
|206|`sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.new`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op206_installed`|
|207|`sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.TRUNC_SIDE`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op207_installed`|
|208|`sha2.core_api.Sha256VarCore.Insts.DigestCore_apiUpdateCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80.update_blocks`|yes|OPEN; `OPEN`|
|209|`block_buffer.Eager.Insts.Block_bufferSealedSealed.split_blocks`|yes|OPEN; `OPEN`|
|210|`block_buffer.Eager.Insts.Block_bufferSealedSealed.invariant`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op210_installed`|
|211|`ArrayT32.Insts.CoreConvertFromGenericArrayTUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplOddTArrayT0.from`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op211_installed`|
|212|`digest.digest.Digest.Blanket.finalize`|yes|OPEN; `OPEN`|
|213|`digest.digest.Digest.Blanket.update`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op213_installed`|
|214|`digest.digest.Digest.Blanket.new`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op214_installed`|
|215|`digest.core_api.wrapper.CoreWrapper.Insts.DigestFixedOutput.finalize_into`|yes|OPEN; `OPEN`|
|216|`digest.core_api.wrapper.CoreWrapper.Insts.DigestUpdate.update`|yes|OPEN; `OPEN`|
|217|`digest.core_api.wrapper.CoreWrapper.Insts.CoreDefaultDefault.default`|yes|OPEN; `OPEN`|
|218|`digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.CoreDefaultDefault.default`|yes|new source interpretation; `R1Z.PDict_CtConstructor.op218_installed`|
|219|`digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.DigestCore_apiFixedOutputCore.finalize_fixed_core`|yes|OPEN; `OPEN`|
|220|`digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.DigestCore_apiUpdateCore.update_blocks`|yes|new source interpretation; `R1Z.PDict_CtUpdate.op220_installed`|
|221|`block_buffer.Eager.Insts.CoreDefaultDefault.default`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op221_installed`|
|222|`aspis_statement.constraints_v4.multilinear_evaluate_qm31`|yes|OPEN; `OPEN`|
|223|`aspis_statement.logup.compress_tagged_tuple`|yes|OPEN; `OPEN`|
|224|`aspis_statement.pool_v1.pair_forest_semantic_oracle.build_pool_v1_pair_forest_copy_helper_v1`|yes|OPEN; `OPEN`|
|225|`aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.transition`|yes|OPEN; `OPEN`|
|226|`aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes`|yes|OPEN; `OPEN`|
|227|`aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31`|yes|OPEN; `OPEN`|
|228|`aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1`|yes|OPEN; `OPEN`|
|229|`aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1.eq`|yes|OPEN; `OPEN`|
|230|`aspis_statement.state_only_semantic.state_only_copy_helper_sum`|yes|OPEN; `OPEN`|
|231|`aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone`|yes|OPEN; `OPEN`|
|232|`aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.p_r1_check`|yes|OPEN; `OPEN`|
|233|`transport.Variant.Insts.CoreCmpPartialEqVariant.eq`|yes|inherited source interpretation; `inherited selection`|
|234|`transport.Variant.tag`|yes|inherited source interpretation; `inherited selection`|
|235|`multiproof.LEAF_BITS`|yes|new source interpretation; `R1Z.PDict_PureDictionary.op235_installed`|
|236|`multiproof.MAX_BATCH`|yes|new source interpretation; `R1Z.PDict_PureDictionary.op236_installed`|
|237|`compact.SLOT_NODES`|yes|inherited source interpretation; `inherited selection`|
|238|`host_commitment.clear_private_salt`|no|new source interpretation; `R1Z.PDict_ResumeDictionary.op238_installed`; `R1Z.PDict_ReachCaller.op238_irrelevant`|
|239|`r1_wire.CLAIMS`|yes|new source interpretation; `R1Z.PDict_PureDictionary.op239_installed`|
|240|`r1_wire.LANES`|yes|new source interpretation; `R1Z.PDict_PureDictionary.op240_installed`|
|241|`compact.LOGICAL_SEMANTIC`|yes|inherited source interpretation; `inherited selection`|
|242|`compact.PROOF_BYTES`|yes|inherited source interpretation; `inherited selection`|
|243|`compact.OFF_NODES`|yes|inherited source interpretation; `inherited selection`|
|244|`compact.OFF_OPENINGS`|yes|inherited source interpretation; `inherited selection`|
|245|`compact.MAGIC`|yes|inherited source interpretation; `inherited selection`|
|246|`multiproof.binary_parent`|yes|OPEN; `OPEN`|
|247|`trace.value`|yes|OPEN; `OPEN`|
|248|`sampler.qm31_sample`|yes|inherited source interpretation; `inherited selection`|
|249|`sampler.gamma_sample`|yes|OPEN; `OPEN`|
|250|`sampler.ordinary_sample`|yes|OPEN; `OPEN`|
|251|`weights.Weights.materialize`|yes|OPEN; `OPEN`|
|252|`weights.Weights.new`|yes|OPEN; `OPEN`|
|253|`weights.Weights.raw`|yes|OPEN; `OPEN`|
|254|`weights.powers`|yes|OPEN; `OPEN`|
|255|`transport.Variant.coefficients`|yes|OPEN; `OPEN`|
|256|`r1_wire.Error.Insts.CoreCmpPartialEqError.eq`|yes|new source interpretation; `R1Z.PDict_ResumeDictionary.op256_installed`|
|257|`host_work.map`|yes|OPEN; `OPEN`|
|258|`ct_pole.all_slots_clear`|yes|OPEN; `OPEN`|
|259|`sampler.circle_sample`|yes|OPEN; `OPEN`|
|260|`r1_wire.DOMAIN`|yes|new source interpretation; `R1Z.PDict_PureDictionary.op260_installed`|
|261|`std.fs.File.Insts.StdIoWrite.write_all`|yes|OPEN; `OPEN`|

## Types

| ID | Name | Status / evidence |
|---:|---|---|
|0|`std.fs.File`|installed value/source representation; `R1Z.PDict_FileCarrier.type0_installed`; P6 descriptor value codec for an already-live Unix File owner; does not create OS ownership; native world/Drop transport remains separate|
|1|`std.fs.OpenOptions`|installed value/source representation; `R1Z.PDict_FinalTypes.type1_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|2|`std.path.Path`|installed value/source representation; `R1Z.PDict_FinalTypes.type2_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|3|`std.io.error.Error`|OPEN; `open`; PDict_OwnedErrorSource and PDict_OwnedErrorCorrect: non-dynamic reference extracted and proved;15 scoped Kani runs,12 pass. Universal reachable-native quotient, ownership/world and full caller composition remain open; not a native type binding.|
|4|`std.path.PathBuf`|installed value/source representation; `R1Z.PDict_FinalTypes.type4_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|5|`alloc.collections.TryReserveError`|installed value/source representation; `R1Z.PDict_FinalTypes.type5_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|6|`aspis_core.state_only_prefix.r0.Error`|installed value/source representation; `R1Z.PDict_FinalTypes.type6_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|7|`getrandom.error.Error`|installed value/source representation; `R1Z.PDict_FinalTypes.type7_installed`; P6 complete signed32 value codec; no entropy/ABI/Drop composition|
|8|`aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1`|installed value/source representation; `R1Z.PDict_FinalTypes.type8_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|9|`typenum.uint.UInt`|installed value/source representation; `R1Z.PDict_FinalTypes.type9_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|10|`sha2.core_api.Sha256VarCore`|installed value/source representation; `R1Z.PDict_FinalTypes.type10_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|11|`generic_array.GenericArray`|installed value/source representation; `R1Z.PDict_FinalTypes.type11_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|12|`generic_array.GenericArrayImplOdd`|installed value/source representation; `R1Z.PDict_FinalTypes.type12_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|13|`generic_array.GenericArrayImplEven`|installed value/source representation; `R1Z.PDict_FinalTypes.type13_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|14|`block_buffer.BlockBuffer`|installed value/source representation; `R1Z.PDict_FinalTypes.type14_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|15|`digest.core_api.wrapper.CoreWrapper`|installed value/source representation; `R1Z.PDict_FinalTypes.type15_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|16|`digest.core_api.ct_variable.CtVariableCoreWrapper`|installed value/source representation; `R1Z.PDict_FinalTypes.type16_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|17|`aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1`|installed value/source representation; `R1Z.PDict_FinalTypes.type17_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|18|`aspis_statement.pool_v1.pair_trace.PoolV1PairTracePublicOutputsV1`|installed value/source representation; `R1Z.PDict_FinalTypes.type18_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|19|`aspis_statement.pool_v1.pair_trace.PoolV1PairTraceVariantV1`|installed value/source representation; `R1Z.PDict_FinalTypes.type19_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|20|`aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1`|installed value/source representation; `R1Z.PDict_FinalTypes.type20_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|21|`aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1`|installed value/source representation; `R1Z.PDict_FinalTypes.type21_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|22|`aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1`|installed value/source representation; `R1Z.PDict_FinalTypes.type22_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|23|`aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1`|installed value/source representation; `R1Z.PDict_FinalTypes.type23_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|24|`aspis_statement.pool_v1.pair_trace.PoolV1PairCopyWeightV1`|installed value/source representation; `R1Z.PDict_FinalTypes.type24_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|25|`weights.Weights`|installed value/source representation; `R1Z.PDict_FinalTypes.type25_installed`; D188 transparent type extraction; existing std/Allocator Vec/Layout models where used|
|26|`F64`|installed value/source representation; `R1Z.PDict_FinalTypes.type26_installed`; P6 complete64-bit float codec; no floating arithmetic interpretation|
|27|`core.fmt.Formatter`|OPEN; `open`; Seven source callbacks erased; PDict_FormatterDictionaryMap retypes all262 fields with structural carrier/trait maps; store/path transport checked. Whole caller transport and native carrier/effects remain open.|

File value representation does not supply OS authority or world transport. New File ABI checks retain their stated finite schedules; arbitrary retries, open/create_new/mode, dynamic payload/vtables, side channels, native-world/Drop composition and whole RunJoin remain open. Serializer op51 retains its callback because iterator/chunk templates are unselected. No simulator, observer, bad event, seed, adversary, witness, protocol, shipped source, artifact pin or root theorem changed.
