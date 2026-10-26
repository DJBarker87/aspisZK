# Installed and remaining prover dictionary entries

Target not yet established. Zero root refinement premises removed. These tables describe the final simultaneous partial source/value dictionary.

New source entries:93; inherited:62; selected:155/262. Remaining:107, including19 outer-reachable entries outside the proof-body reachability overapproximation. Type interpretations:25/28; remaining0,3,27.

## Newly installed entries

| ID | Name | Theorem |
|---:|---|---|
|0|`Shared0T.Insts.CoreConvertAsRef.as_ref`|`R1Z.PDict_ResumeDictionary.op0_installed`|
|1|`Slice.Insts.CoreConvertAsRefSlice.as_ref`|`R1Z.PDict_ResumeDictionary.op1_installed`|
|2|`core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq`|`R1Z.PDict_ResumeDictionary.op2_installed`|
|13|`core.sync.atomic.compiler_fence`|`R1Z.PDict_ResumeDictionary.op13_installed`|
|19|`std.fs.OpenOptions.new`|`R1Z.PDict_ResumeDictionary.op19_installed`|
|20|`std.fs.OpenOptions.write`|`R1Z.PDict_ResumeDictionary.op20_installed`|
|21|`std.fs.OpenOptions.create_new`|`R1Z.PDict_ResumeDictionary.op21_installed`|
|24|`std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode`|`R1Z.PDict_ResumeDictionary.op24_installed`|
|27|`std.path.Path.Insts.CoreConvertAsRefPath.as_ref`|`R1Z.PDict_ResumeDictionary.op27_installed`|
|124|`aspis_prover.state_only_hiding.volatile_clear_cell`|`R1Z.PDict_VolatileCell.op124_installed`|
|125|`zeroize.Zeroizing.Insts.CoreConvertAsMut.as_mut`|`R1Z.PDict_OffpathBorrow.op125_installed`|
|126|`zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut`|`R1Z.PDict_OffpathBorrow.op126_installed`|
|135|`typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUTermSoFarSoFar.private_cmp`|`R1Z.PDict_ResumeDictionary.op135_installed`|
|136|`typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUIntSoFarLess.private_cmp`|`R1Z.PDict_ResumeDictionary.op136_installed`|
|137|`typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB0SoFarClause3_Output.private_cmp`|`R1Z.PDict_ResumeDictionary.op137_installed`|
|138|`typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB1SoFarClause3_Output.private_cmp`|`R1Z.PDict_ResumeDictionary.op138_installed`|
|139|`typenum.uint.UIntUlB0.Insts.TypenumPrivatePrivateCmpUIntUrB0SoFarClause3_Output.private_cmp`|`R1Z.PDict_ResumeDictionary.op139_installed`|
|140|`typenum.uint.UIntUlB0.Insts.TypenumType_operatorsCmpUIntUrB0Clause2_Output.compare`|`R1Z.PDict_ResumeDictionary.op140_installed`|
|141|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_isize`|`R1Z.PDict_ResumeDictionary.op141_installed`|
|142|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i64`|`R1Z.PDict_ResumeDictionary.op142_installed`|
|143|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i32`|`R1Z.PDict_ResumeDictionary.op143_installed`|
|144|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i16`|`R1Z.PDict_ResumeDictionary.op144_installed`|
|145|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i8`|`R1Z.PDict_ResumeDictionary.op145_installed`|
|146|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_usize`|`R1Z.PDict_ResumeDictionary.op146_installed`|
|147|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u64`|`R1Z.PDict_ResumeDictionary.op147_installed`|
|148|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u32`|`R1Z.PDict_ResumeDictionary.op148_installed`|
|149|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u16`|`R1Z.PDict_ResumeDictionary.op149_installed`|
|150|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u8`|`R1Z.PDict_ResumeDictionary.op150_installed`|
|151|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.ISIZE`|`R1Z.PDict_ResumeDictionary.op151_installed`|
|152|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I64`|`R1Z.PDict_ResumeDictionary.op152_installed`|
|153|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I32`|`R1Z.PDict_ResumeDictionary.op153_installed`|
|154|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I16`|`R1Z.PDict_ResumeDictionary.op154_installed`|
|155|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I8`|`R1Z.PDict_ResumeDictionary.op155_installed`|
|156|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.USIZE`|`R1Z.PDict_ResumeDictionary.op156_installed`|
|157|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U64`|`R1Z.PDict_ResumeDictionary.op157_installed`|
|158|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U32`|`R1Z.PDict_ResumeDictionary.op158_installed`|
|159|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U16`|`R1Z.PDict_ResumeDictionary.op159_installed`|
|160|`typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U8`|`R1Z.PDict_ResumeDictionary.op160_installed`|
|161|`typenum.uint.UInt.Insts.CoreDefaultDefault.default`|`R1Z.PDict_ResumeDictionary.op161_installed`|
|162|`typenum.uint.UInt.Insts.CoreCloneClone.clone`|`R1Z.PDict_ResumeDictionary.op162_installed`|
|163|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_isize`|`R1Z.PDict_ResumeDictionary.op163_installed`|
|164|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i64`|`R1Z.PDict_ResumeDictionary.op164_installed`|
|165|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i32`|`R1Z.PDict_ResumeDictionary.op165_installed`|
|166|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i16`|`R1Z.PDict_ResumeDictionary.op166_installed`|
|167|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i8`|`R1Z.PDict_ResumeDictionary.op167_installed`|
|168|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_usize`|`R1Z.PDict_ResumeDictionary.op168_installed`|
|169|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u64`|`R1Z.PDict_ResumeDictionary.op169_installed`|
|170|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u32`|`R1Z.PDict_ResumeDictionary.op170_installed`|
|171|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u16`|`R1Z.PDict_ResumeDictionary.op171_installed`|
|172|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u8`|`R1Z.PDict_ResumeDictionary.op172_installed`|
|173|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.ISIZE`|`R1Z.PDict_ResumeDictionary.op173_installed`|
|174|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I64`|`R1Z.PDict_ResumeDictionary.op174_installed`|
|175|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I32`|`R1Z.PDict_ResumeDictionary.op175_installed`|
|176|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I16`|`R1Z.PDict_ResumeDictionary.op176_installed`|
|177|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I8`|`R1Z.PDict_ResumeDictionary.op177_installed`|
|178|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.USIZE`|`R1Z.PDict_ResumeDictionary.op178_installed`|
|179|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U64`|`R1Z.PDict_ResumeDictionary.op179_installed`|
|180|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U32`|`R1Z.PDict_ResumeDictionary.op180_installed`|
|181|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U16`|`R1Z.PDict_ResumeDictionary.op181_installed`|
|182|`typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U8`|`R1Z.PDict_ResumeDictionary.op182_installed`|
|183|`typenum.uint.UTerm.Insts.CoreDefaultDefault.default`|`R1Z.PDict_ResumeDictionary.op183_installed`|
|184|`typenum.uint.UTerm.Insts.CoreCloneClone.clone`|`R1Z.PDict_ResumeDictionary.op184_installed`|
|185|`typenum.type_operators.IsLessOrEqual.Blanket.is_less_or_equal`|`R1Z.PDict_ResumeDictionary.op185_installed`|
|186|`typenum.type_operators.IsLess.Blanket.is_less`|`R1Z.PDict_ResumeDictionary.op186_installed`|
|187|`typenum.private.IsLessOrEqualPrivateABEqualB1.Blanket.is_less_or_equal_private`|`R1Z.PDict_ResumeDictionary.op187_installed`|
|188|`typenum.bit.B1.Insts.TypenumMarker_traitsBit.to_bool`|`R1Z.PDict_ResumeDictionary.op188_installed`|
|189|`typenum.bit.B1.Insts.TypenumMarker_traitsBit.to_u8`|`R1Z.PDict_ResumeDictionary.op189_installed`|
|190|`typenum.bit.B1.Insts.TypenumMarker_traitsBit.new`|`R1Z.PDict_ResumeDictionary.op190_installed`|
|191|`typenum.bit.B1.Insts.TypenumMarker_traitsBit.BOOL`|`R1Z.PDict_ResumeDictionary.op191_installed`|
|192|`typenum.bit.B1.Insts.TypenumMarker_traitsBit.U8`|`R1Z.PDict_ResumeDictionary.op192_installed`|
|193|`typenum.bit.B1.Insts.CoreDefaultDefault.default`|`R1Z.PDict_ResumeDictionary.op193_installed`|
|194|`typenum.bit.B1.Insts.CoreCloneClone.clone`|`R1Z.PDict_ResumeDictionary.op194_installed`|
|195|`typenum.private.IsLessPrivateABLessB1.Blanket.is_less_private`|`R1Z.PDict_ResumeDictionary.op195_installed`|
|196|`typenum.Equal.Insts.TypenumMarker_traitsOrd.to_ordering`|`R1Z.PDict_ResumeDictionary.op196_installed`|
|197|`typenum.Greater.Insts.TypenumMarker_traitsOrd.to_ordering`|`R1Z.PDict_ResumeDictionary.op197_installed`|
|198|`typenum.bit.B0.Insts.TypenumMarker_traitsBit.to_bool`|`R1Z.PDict_ResumeDictionary.op198_installed`|
|199|`typenum.bit.B0.Insts.TypenumMarker_traitsBit.to_u8`|`R1Z.PDict_ResumeDictionary.op199_installed`|
|200|`typenum.bit.B0.Insts.TypenumMarker_traitsBit.new`|`R1Z.PDict_ResumeDictionary.op200_installed`|
|201|`typenum.bit.B0.Insts.TypenumMarker_traitsBit.BOOL`|`R1Z.PDict_ResumeDictionary.op201_installed`|
|202|`typenum.bit.B0.Insts.TypenumMarker_traitsBit.U8`|`R1Z.PDict_ResumeDictionary.op202_installed`|
|203|`typenum.bit.B0.Insts.CoreDefaultDefault.default`|`R1Z.PDict_ResumeDictionary.op203_installed`|
|204|`typenum.bit.B0.Insts.CoreCloneClone.clone`|`R1Z.PDict_ResumeDictionary.op204_installed`|
|206|`sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.new`|`R1Z.PDict_ResumeDictionary.op206_installed`|
|207|`sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.TRUNC_SIDE`|`R1Z.PDict_ResumeDictionary.op207_installed`|
|210|`block_buffer.Eager.Insts.Block_bufferSealedSealed.invariant`|`R1Z.PDict_ResumeDictionary.op210_installed`|
|211|`ArrayT32.Insts.CoreConvertFromGenericArrayTUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplOddTArrayT0.from`|`R1Z.PDict_ResumeDictionary.op211_installed`|
|213|`digest.digest.Digest.Blanket.update`|`R1Z.PDict_ResumeDictionary.op213_installed`|
|214|`digest.digest.Digest.Blanket.new`|`R1Z.PDict_ResumeDictionary.op214_installed`|
|218|`digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.CoreDefaultDefault.default`|`R1Z.PDict_CtConstructor.op218_installed`|
|220|`digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.DigestCore_apiUpdateCore.update_blocks`|`R1Z.PDict_CtUpdate.op220_installed`|
|221|`block_buffer.Eager.Insts.CoreDefaultDefault.default`|`R1Z.PDict_ResumeDictionary.op221_installed`|
|238|`host_commitment.clear_private_salt`|`R1Z.PDict_ResumeDictionary.op238_installed`|
|256|`r1_wire.Error.Insts.CoreCmpPartialEqError.eq`|`R1Z.PDict_ResumeDictionary.op256_installed`|

## Type interpretations

| ID | Name | Status and theorem |
|---:|---|---|
|0|`std.fs.File`|OPEN; `no theorem`|
|1|`std.fs.OpenOptions`|installed value/source representation; `R1Z.PDict_FinalTypes.type1_installed`|
|2|`std.path.Path`|installed value/source representation; `R1Z.PDict_FinalTypes.type2_installed`|
|3|`std.io.error.Error`|OPEN; `no theorem`|
|4|`std.path.PathBuf`|installed value/source representation; `R1Z.PDict_FinalTypes.type4_installed`|
|5|`alloc.collections.TryReserveError`|installed value/source representation; `R1Z.PDict_FinalTypes.type5_installed`|
|6|`aspis_core.state_only_prefix.r0.Error`|installed value/source representation; `R1Z.PDict_FinalTypes.type6_installed`|
|7|`getrandom.error.Error`|installed value/source representation; `R1Z.PDict_FinalTypes.type7_installed`|
|8|`aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1`|installed value/source representation; `R1Z.PDict_FinalTypes.type8_installed`|
|9|`typenum.uint.UInt`|installed value/source representation; `R1Z.PDict_FinalTypes.type9_installed`|
|10|`sha2.core_api.Sha256VarCore`|installed value/source representation; `R1Z.PDict_FinalTypes.type10_installed`|
|11|`generic_array.GenericArray`|installed value/source representation; `R1Z.PDict_FinalTypes.type11_installed`|
|12|`generic_array.GenericArrayImplOdd`|installed value/source representation; `R1Z.PDict_FinalTypes.type12_installed`|
|13|`generic_array.GenericArrayImplEven`|installed value/source representation; `R1Z.PDict_FinalTypes.type13_installed`|
|14|`block_buffer.BlockBuffer`|installed value/source representation; `R1Z.PDict_FinalTypes.type14_installed`|
|15|`digest.core_api.wrapper.CoreWrapper`|installed value/source representation; `R1Z.PDict_FinalTypes.type15_installed`|
|16|`digest.core_api.ct_variable.CtVariableCoreWrapper`|installed value/source representation; `R1Z.PDict_FinalTypes.type16_installed`|
|17|`aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1`|installed value/source representation; `R1Z.PDict_FinalTypes.type17_installed`|
|18|`aspis_statement.pool_v1.pair_trace.PoolV1PairTracePublicOutputsV1`|installed value/source representation; `R1Z.PDict_FinalTypes.type18_installed`|
|19|`aspis_statement.pool_v1.pair_trace.PoolV1PairTraceVariantV1`|installed value/source representation; `R1Z.PDict_FinalTypes.type19_installed`|
|20|`aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1`|installed value/source representation; `R1Z.PDict_FinalTypes.type20_installed`|
|21|`aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1`|installed value/source representation; `R1Z.PDict_FinalTypes.type21_installed`|
|22|`aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1`|installed value/source representation; `R1Z.PDict_FinalTypes.type22_installed`|
|23|`aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1`|installed value/source representation; `R1Z.PDict_FinalTypes.type23_installed`|
|24|`aspis_statement.pool_v1.pair_trace.PoolV1PairCopyWeightV1`|installed value/source representation; `R1Z.PDict_FinalTypes.type24_installed`|
|25|`weights.Weights`|installed value/source representation; `R1Z.PDict_FinalTypes.type25_installed`|
|26|`F64`|installed value/source representation; `R1Z.PDict_FinalTypes.type26_installed`|
|27|`core.fmt.Formatter`|OPEN; `no theorem`|

## Remaining function entries

Body-reachable entries remain with the sibling except the closed semantic-error equality. This syntactic overapproximation also includes error branches; it is not an honest-run restriction. Native implicit Drop reachability is not captured by this source reference scan.

| ID | Name | In body overapproximation |
|---:|---|---|
|3|`core.mem.take`|True|
|4|`core.mem.drop`|True|
|5|`core.option.Option.is_some_and`|True|
|6|`core.option.Option.as_ref`|True|
|7|`core.option.Option.ok_or`|True|
|8|`core.option.Option.Insts.CoreCmpPartialEqOption.eq`|True|
|9|`core.option.Option.Insts.CoreOpsTry_traitTry.branch`|True|
|10|`core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual`|True|
|11|`core.result.Result.map`|True|
|14|`std.fs.File.open`|False|
|15|`std.fs.File.sync_all`|False|
|16|`std.io.Write.write_all.default`|False|
|17|`std.fs.File.Insts.StdIoWrite.flush`|False|
|18|`std.fs.File.Insts.StdIoWrite.write`|False|
|22|`std.fs.OpenOptions.open`|False|
|23|`std.io.error.Error.kind`|False|
|25|`std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref`|False|
|26|`std.path.Path.join`|False|
|28|`alloc.string.String.Insts.CoreConvertAsRefPath.as_ref`|False|
|29|`std.path.PathBuf.Insts.CoreConvertAsRefPath.as_ref`|False|
|30|`alloc.string.String.with_capacity`|False|
|31|`alloc.string.String.push_str`|False|
|32|`alloc.vec.Vec.try_reserve_exact`|True|
|33|`alloc.vec.Vec.pop`|True|
|34|`alloc.vec.Vec.is_empty`|True|
|35|`alloc.vec.Vec.Insts.CoreDefaultDefault.default`|True|
|36|`Array.Insts.CoreConvertTryFromVecVec.try_from`|True|
|37|`aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq`|True|
|40|`aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone.clone`|True|
|41|`aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq`|True|
|43|`aspis_core.field.wide_exact.WideExact.impl.c0`|True|
|44|`aspis_core.field.wide_exact.WideExact.impl.c1`|True|
|49|`aspis_core.field.wide_exact.WideExact.to_limbs`|True|
|50|`aspis_core.field.wide_exact.WideExact.from_le_bytes`|True|
|51|`aspis_core.field.wide_exact.WideExact.to_le_bytes`|True|
|60|`aspis_core.field.CM31.new`|True|
|71|`aspis_core.field.QM31.from_le_bytes`|True|
|72|`aspis_core.field.QM31.write_le_bytes`|True|
|77|`aspis_core.r0.domain.Point.Insts.CoreCloneClone.clone`|True|
|78|`aspis_core.r0.domain.fibre_point`|True|
|79|`aspis_core.r0.encoder.eval_message`|True|
|80|`aspis_core.r0.fold.phi_inverse`|True|
|81|`aspis_core.r0.heap.filled`|True|
|82|`aspis_core.r0.merkle.C1_TAG`|True|
|83|`aspis_core.r0.merkle.C2_TAG`|True|
|84|`aspis_core.r0.merkle.leaf`|True|
|85|`aspis_core.r0.Error.Insts.CoreFmtDebug.fmt`|False|
|86|`aspis_core.r0.opening.LANES`|True|
|100|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.neg`|True|
|101|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.neg`|True|
|105|`aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv`|True|
|107|`aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.try_inv`|True|
|109|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.try_inv`|True|
|110|`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31`|True|
|111|`aspis_core.state_only_hiding.PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT`|True|
|114|`aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext.eq`|True|
|117|`aspis_core.state_only_hiding.state_only_selected_mask_value`|True|
|118|`aspis_core.state_only_prefix.r0.statement_points`|True|
|120|`aspis_core.state_only_sumcheck.state_only_boundary_sum`|True|
|121|`aspis_core.state_only_sumcheck.evaluate_state_only_polynomial`|True|
|122|`Array.Insts.ZeroizeZeroize.zeroize`|True|
|123|`zeroize.Zeroize.Blanket.zeroize`|True|
|127|`zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref`|True|
|128|`zeroize.Zeroizing.new`|True|
|129|`getrandom.fill`|False|
|130|`zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize`|True|
|131|`zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref`|True|
|132|`aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1`|True|
|133|`aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_rows_v1`|True|
|134|`aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1`|True|
|205|`sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.finalize_variable_core`|False|
|208|`sha2.core_api.Sha256VarCore.Insts.DigestCore_apiUpdateCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80.update_blocks`|False|
|209|`block_buffer.Eager.Insts.Block_bufferSealedSealed.split_blocks`|False|
|212|`digest.digest.Digest.Blanket.finalize`|False|
|215|`digest.core_api.wrapper.CoreWrapper.Insts.DigestFixedOutput.finalize_into`|False|
|216|`digest.core_api.wrapper.CoreWrapper.Insts.DigestUpdate.update`|False|
|217|`digest.core_api.wrapper.CoreWrapper.Insts.CoreDefaultDefault.default`|False|
|219|`digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.DigestCore_apiFixedOutputCore.finalize_fixed_core`|False|
|222|`aspis_statement.constraints_v4.multilinear_evaluate_qm31`|True|
|223|`aspis_statement.logup.compress_tagged_tuple`|True|
|224|`aspis_statement.pool_v1.pair_forest_semantic_oracle.build_pool_v1_pair_forest_copy_helper_v1`|True|
|225|`aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.transition`|True|
|226|`aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes`|True|
|227|`aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31`|True|
|228|`aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1`|True|
|229|`aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1.eq`|True|
|230|`aspis_statement.state_only_semantic.state_only_copy_helper_sum`|True|
|231|`aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone`|True|
|232|`aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.p_r1_check`|True|
|235|`multiproof.LEAF_BITS`|True|
|236|`multiproof.MAX_BATCH`|True|
|239|`r1_wire.CLAIMS`|True|
|240|`r1_wire.LANES`|True|
|246|`multiproof.binary_parent`|True|
|247|`trace.value`|True|
|249|`sampler.gamma_sample`|True|
|250|`sampler.ordinary_sample`|True|
|251|`weights.Weights.materialize`|True|
|252|`weights.Weights.new`|True|
|253|`weights.Weights.raw`|True|
|254|`weights.powers`|True|
|255|`transport.Variant.coefficients`|True|
|257|`host_work.map`|True|
|258|`ct_pole.all_slots_clear`|True|
|259|`sampler.circle_sample`|True|
|260|`r1_wire.DOMAIN`|True|
|261|`std.fs.File.Insts.StdIoWrite.write_all`|False|

All E1/E2, carrier, adversary, witness, bad-event, seed and observer requirements remain unchanged. File ownership and dynamic IO-error/formatter representations are open. No complete native dictionary, root RunJoin, privacy,100-bit or adoption claim is made.
