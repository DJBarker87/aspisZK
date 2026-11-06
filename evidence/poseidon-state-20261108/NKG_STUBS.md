# NKG child calls and domains

All native outlines replace child calls with local unconstrained typed reply logs, never arithmetic implementations. The complete packet root chooses the actual emitted child's reply and internally proves its success/domain on the SAME logged arguments. No field multiplication is evaluated in Kani. The table names the corresponding Lean laws; imported names resolve through the pinned coherent objects (RPv_ aliases where used). Exact statements/imports are in the module snapshots and L051 output.

| Native child stub / source call | Lean law paired with actual emitted reply | Domain established in parent |
|---|---|---|
| NKG scalar interpolation, 321 | NHU_Interpolation.result; NKG_ColumnTotal.step_total; NKG_ColumnReply.result | SAME three canonical weights, SAME three M31 constants <2147483647 and finite lane |
| NKG dot7, 324 | NFT_DotSource.source; NKG_InternalSource.result | Both SAME slices length7, canonical weights and constants from actual ROM |
| NKG internal round, 324 | NIH_InternalRound.result; NKG_InternalChoices.value | SAME canonical state and exact interpolated scalar, second state first reply |
| NKG constant columns, 323 | NKG_ColumnsPacket.source; NKG_FullSource.result | SAME selectors1/9/10 and six fixed ROM rows, all canonical |
| NKG full rounds, 323 | NIH_FullRounds.qm / packed_qm; NKG_FullChoices.value | SAME canonical state and constants; complete intermediate state |
| NKG low addition, 308 | FIv_PreparedTotal.add; NKG_LowTotal.fold; NKG_LowFrame.loop | Canonical SAME accumulator and selector coordinate; finite3/7 induction |
| NKG leading/full/internal branches, 308 | NIH_Leading.result; NKG_FullPacket.source; NKG_InternalPacket.source; NKG_OracleChoices.ready | Original openings/selector arrays canonical; all branch arguments preserved |
| NKG prepared constructors, 308 | existing FIt/FIv prepared-new source laws; NKG_PreparedMap.result; NKG_PreparedRaw.source/native | Canonical SAME three low weights and block selector; every raw9 cache word preserved; PreparedFor derived |
| NKG pack, 308 | JFy_ArrayTotal read/slice laws; NKG_SliceTotal.pack; NKG_CellTotal.cell | Exact four-coordinate window for g<4, original canonical succ/internal states |
| NKG subtract3, 308 | JFy_FieldTotal.sub; NKG_AfterTotal.result | Canonical SAME target and both pack replies/internal value |
| NKG prepared sum3, 308 | FJe_Sum3WrapperBridge and existing value law; NKG_Sum3Total.result | SAME three canonical differences and PreparedFor SAME three low weights |
| NKG prepared block multiply, 308 | FIv_PreparedTotal.mul (through FIv_PreparedMul.mapped/value and emitted FIq_Native definition); NKG_AfterTotal.result | PreparedFor SAME raw block and canonical SAME sum reply; value exactly decode(block selector)*decode(sum) |
| NKG final array callback, 308 | NKG_BuilderRaw.reply_ok/source | Exact SAME four callbacks, complete raw output array |

The prepared block multiplication is an additive exact-source inventory correction: baseline308 lists generic `.mul` alternatives but omits `PreparedQm31Multiplier::mul`. It has no standalone baseline ledger row. It is discharged here under field-product rule A by the named emitted Lean law and the native K044–046 forwarding cut, not an invented CLOSED row. The original alternatives remain visible in NKG_ROW_PACKETS.json. Existing Std/allocator/ABI/source-to-ELF trust remains under (au) and option A; no new trust row is introduced.

Caller canonicality and prepared-cache properties are derived in NKG_HelperDomains, NKG_OracleChoices.ready, NKG_CellTotal and NKG_AfterTotal. There is no root assumption of any child Result, output equality, source Run or arbitrary Ops dictionary. The root native cuts remain the explicit reviewed semantic-transport premises.
