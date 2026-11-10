# PCVG_TRUST_ROWS: DRAFT trust-row text, library rows (2026-11-10)

Target not yet established. DRAFT TEXT ONLY. No row has been added to any document; nothing is removed or reclassified. Basis: owner decision 2026-11-10, the trust boundary is the frozen Aspis source; Rust core/alloc/std, the Solana SDK crates, the compiler/linker and runtime syscalls are trust by named row, not proof work. Form follows HM-A and HM-B in evidence/prov-p6r-20261110/PCXD_TRUST_PROPOSALS.md. Members are exact Lean names read from that file; reach and CLOSED-row counts there are carried by reference (PCXD_TRUST_PROPOSALS.md, same row letter), not recomputed. HM-M (array_from_fn_copy) and HM-N/HM-O are not here: HM-M stays a proof item.

Pins. Frozen Cargo.lock (4bb3b3f): solana-pubkey 2.4.0, solana-hash 2.3.0, solana-program-error 2.2.2, solana-sdk-ids 2.2.1. Rust core/alloc: the toolchain sysroot recorded in the PCQ_*_PINS.json files (quoted in the proposals as nightly-2026-06-01); the client toolchain 1.94.1 is separately pinned by owner decision 2026-10-27. These two toolchain strings come from the earlier proposals and the NPE_ run (which used nightly-2026-09-17 and 1.94.1); the row owner must confirm which sysroot the extraction used before the row is entered.

Residual common to every row: the row says each Lean model matches the cited Rust item on the behaviour the Aspis consumers use. It is not proved. The differential-check column (item C) says where a compiled test exists; no row has proof of library behaviour behind it.

## PROPOSED-HM-C: Option/Result combinators

**Statement.** The Lean definitions of Option::ok_or, Result::map, Result::map_err, the Option Try::branch and FromResidual::from_residual instances and the Option equality instance, together with the alloc TryReserveError type, are accepted as the Rust core/alloc semantics of those items at the pinned sysroot, for the instantiations Aspis code uses.

**Members (exact Lean names).** `core.option.Option.ok_or`; `core.result.Result.map`; `core.result.Result.map_err`; `core.option.Option.Insts.CoreOpsTry_traitTry.branch`; `core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual`; `core.option.Option.Insts.CoreCmpPartialEqOption.eq`; `alloc.collections.TryReserveError`. Gate-side copies in a module namespace (for example `FIo_Native.core.*`, `AspisS1NativeCompact.core.option.Option.ok_or`) carry the same row.

**Consumers.** 15 gate modules (list in HM-C of PCXD_TRUST_PROPOSALS.md), among them AspisR72Sampler.Funs, AspisR1TerminalDecoder.Funs, NMT_first.Funs, NMT_stage1_owned.Funs, S1NativeCompactModelV1.

**Differential check.** None yet. Candidate (C): small Rust test over Option<u8>/Result<u8,u8> combinators against a Lean evaluation of the models. Not run.

**Removal condition.** Replace by the Aeneas library definitions and one generic equality lemma per combinator (each is a short funext/cases proof; S1NativeCompactModelV1 Option.ok_or already has one, PRVEq_S1NativeCompactModelV1_okor_f1.lean, PCVF_L001). The row stays until the consumers use the Aeneas library definition.

## PROPOSED-HM-D: array and slice operations (excluding from_fn)

**Statement.** The Lean definitions of Array::map, array/slice equality (PartialEq between slice and array), slice windows, slice first, and the RangeFull slice-index operations are accepted as the Rust core semantics at the pinned sysroot, for the instantiations Aeneas code uses. The `core.array.from_fn` stand-in is excluded: it is HM-M and stays a proof item.

**Members.** `core.array.Array.map`; `FIq_Native.core.array.Array.map`; `Slice.Insts.CoreCmpPartialEqArray.eq`; `Slice.Insts.CoreCmpPartialEqArray.ne`; `core.slice.Slice.windows`; `core.slice.Slice.first`; `core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get`, `.get_mut`, `.get_unchecked`, `.get_unchecked_mut`, `.index`, `.index_mut` (the last seven from the unresolved externals, PCVG_EXTERNALS_BY_CRATE.json; the gate has no definition for them yet, so they are members of the row only once a gate model exists, otherwise open library obligations covered by the row's statement).

**Consumers.** NFN_ExtractedGeometry, NFY_Part042, NID_ResumeEmissionFuns, NJA_CountBody, NMT_stage1_owned.Funs, NMT_first.Funs, RPu_FIq_Native08, RPu_FIq_NativeExternal.

**Differential check.** None yet. Candidate: windows/first/map on small arrays versus Lean evaluation.

**Removal condition.** Aeneas library definitions plus a generic lemma per operation, or re-extraction without the operation.

## PROPOSED-HM-F: num/ops/iter models

**Statement.** The Lean definitions of u16 count_ones and trailing_zeros (with their auxiliary lemmas), Range clone, Rev and RangeInclusive folds (revFold, rangeFold, range_clone_usize) and the default Iterator::all/any methods are accepted as the Rust core semantics at the pinned sysroot.

**Members.** `core.num.U16.count_ones`; `core.num.U16.count_ones_aux`; `core.num.U16.count_ones_aux_le`; `core.num.U16.count_ones_nat`; `core.num.U16.count_ones_nat_le`; `core.num.U16.trailing_zeros`; `core.num.U16.trailing_zeros_aux_le`; `core.num.U16.trailing_zeros_nat`; `core.num.U16.trailing_zeros_nat_le`; `core.ops.range.Range.Insts.CoreCloneClone.clone`; `core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.fold`; `core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold`; `core.iter.traits.iterator.Iterator.all.default`; `core.iter.traits.iterator.Iterator.any.default`; `rangeFold`; `range_clone_usize`; `revFold`. (The ShrAmt bridge is HM-L, already verified.)

**Consumers.** NJA_CountBody, RPu_FIq_NativeExternal, NJS_Extract.Funs.

**Differential check.** Feasible and cheap: count_ones and trailing_zeros on all 2^16 u16 values against a compiled Rust program (executable, finite). Not yet run; see PCVG_DIFFCHECK in this directory if it exists.

**Removal condition.** Prove each against the Lean integer library, or re-extract through Aeneas library definitions.

## PROPOSED-HM-G: Aeneas discriminant helpers

**Statement.** The read_discriminant functions and the ImportUnionNamedDiscriminant registration are accepted as the discriminant reading of the corresponding Rust enums. These are Aeneas-tooling post-processing items, not Aspis code, but their enum inputs are Aspis types; the row covers only the discriminant function, not the enum definitions.

**Members.** `pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.read_discriminant`; `pool_v1.pair_forest_semantic_terminal.CompiledVariant.read_discriminant`; `pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.read_discriminant`; `pool_v1.pair_forest_semantic_terminal.r0.Public.read_discriminant`; `state_only_prefix.r0.Error.read_discriminant`; the registration attribute `import_union_discriminant` / `ImportUnionNamedDiscriminant`; the NEV_discriminantVariant instance for `transport.Variant`.

**Consumers.** NEV_AccumulateRaw.Types, NGD_AtG.Types, RPu_FIq_NativeTypes.

**Classification note.** The enums are Aspis-frozen; if the owner reads "prove Aspis's own code" to include the match-to-discriminant correspondence, then the obligation `read_discriminant e = discriminant of the match` per enum is an Aspis-side proof item (small, decidable by cases) and the row should be limited to the registration attribute and `transport.Variant`. Recorded for the lead, not decided here.

**Differential check.** Not applicable (Lean-side tooling; a Rust `as isize` cast on each enum could be compared, not run).

**Removal condition.** Prove each read_discriminant equals the match-based discriminant, or emit the Aeneas-native form.

## Items (B): library externals folded into rows

From PCVG_EXTERNALS_BY_CRATE.json (99 unresolved entries, 55 distinct names): core/alloc/std 15 entries (14 into HM-D, 1 into HM-F), solana 16 entries (into the accepted SDK row HM-A: solana_pubkey ... eq/as_ref/create_program_address/new_from_array/to_bytes, plus `solana_sdk_ids.bpf_loader_upgradeable.id`, solana-sdk-ids 2.2.1, which HM-A does not name today and would need added), aspis frozen 68 entries (41 distinct) stay open obligations.
