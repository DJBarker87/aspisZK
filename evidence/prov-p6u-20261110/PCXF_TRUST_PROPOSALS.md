# PCXF_TRUST_PROPOSALS: proposed trust-row text for hand-written gate models

Target not yet established. PROPOSED TEXT ONLY: no trust row exists or has been added by this job, and none of this changes a ledger row, the RSL or the security contract. A hand model becomes a trust row only if a CLOSED-row root or the deployed_splitB cone reaches it (flags below); an unreached entry is an unused template.

Source: PCXA_HAND_MODELS.json (carried) and PCXF_HAND_MODELS.json, 924 deduplicated (gate module, external name) entries from every *_HAND_MODELS.json of the campaign: 245 hand-written gate models, 601 unresolved externals (no gate definition found in the examined files: open obligations, not models), the rest Aeneas-generated bodies or unclassified. The hand-written flag combines explicit hand_model flags with a text test (no Aeneas Source: doc comment); it is a classification, not an audit of the model bodies. The statement of each model (that it matches the Rust item) is NOT proved anywhere here.

Class (a) and (b) were pre-notified to the owner by zk-11 (SDK type models; core slice iterator model).

## PROPOSED-HM-A: sdk type models

**Statement.** Gate-side Lean types and functions standing for the Solana SDK items Pubkey, Hash, PubkeyError, ProgramError (and their clone/eq/as_ref/create_program_address/new_from_array/to_bytes methods) are accepted as faithful models of the pinned crates solana-pubkey 2.4.0, solana-hash 2.3.0 and solana-program-error 2.2.2 (frozen Cargo.lock) on exactly the behaviour the consumers use.

**Members.** 6 entries, 5 distinct names in 4 gate modules. Reached by the deployed_splitB cone: 3 by a cone constant of the same short name, 5 by gate module. Reached by a CLOSED-row root module: 6. CLOSED rows touched (module or constant route, first 12 of 42): TX1:168, TX1:169, TX1:170, TX1:186, TX1:328, TX1:329, TX1:330, TX1:333, TX1:335, TX1:336, TX1:337, TX1:338.

**Names.** `ProgramError (type, replaced by alias)`; `solana_hash.Hash`; `solana_hash.Hash.to_bytes`; `solana_program_error.ProgramError.Insts.CoreCloneClone.clone`; `solana_pubkey.Pubkey`

**Pinned crate and version.** aspis-r1-cost-probe or aspis-statement (workspace member of the frozen tree 4bb3b3f) (others: see JSON)

**Consumers.** gate modules: AspisR1WithdrawalCaller.Types, NHJ_SnapshotReference.Types, NMT_first.Funs, NMT_stage1_owned.Funs.

**Removal condition.** Remove when the SDK items are given as extracted-and-compared definitions of the pinned crate versions (a P1 extraction of those crate functions plus Lean equality), or when each consumer is shown to use only the byte-array content (Array U8 32) so that the model is the identity. Note the P0 finding: in the pilot the fresh emission has solana_pubkey.Pubkey as an external axiom and the gate has Array U8 32; the equality is not proved.

## PROPOSED-HM-B: core slice iterator model

**Statement.** The gate definitions for core::slice::chunks_exact_mut and ChunksExactMut::next (as P6ToBytes.StdModel.MutableIterator in AspisR1WideToBytesSource.Funs and the same-named externals elsewhere), together with the core array and slice iterator instances (Iter, IterMut, IntoIter, into_iter, next_back), are accepted as models of the Rust core library iterators at the pinned nightly sysroot.

**Members.** 25 entries, 13 distinct names in 10 gate modules. Reached by the deployed_splitB cone: 20 by a cone constant of the same short name, 24 by gate module. Reached by a CLOSED-row root module: 24. CLOSED rows touched (module or constant route, first 12 of 145): TX1:017, TX1:020, TX1:029, TX1:030, TX1:035, TX1:038, TX1:045, TX1:046, TX1:049, TX1:050, TX1:051, TX1:052.

**Names.** `Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter`; `MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter`; `core.array.iter.IntoIter`; `core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next`; `core.slice.Slice.chunks_exact_mut`; `core.slice.iter.ChunksExactMut`; `core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice.next`; `core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back`; `core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all`; `core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any`; `core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.all`; `core.slice.iter.Windows`; `core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next`

**Pinned crate and version.** Rust core library, rustc nightly-2026-06-01 sysroot (tool pin PCQ_*_PINS.json; no crate version) (others: see JSON)

**Consumers.** gate modules: AspisR1WideToBytesIndexedCandidate.FunsNoResourceOptions, AspisR1WideToBytesSource.Funs, NEI_PushRaw.Funs, NID_ResumeEmissionFuns, NJA_CountBody, NJA_Multiproof.Types, RPu_FIq_NativeExternal, RPu_FIq_NativeTypes, RPz7_WAdm_Fissioned_Funs, RPz7_WAdm_Fissioned_Types.

**Removal condition.** Remove when the iterator models are replaced by Aeneas library definitions proved equal to a Lean specification of the std semantics, or when the consumers (WideToBytes and the loop-based decoders) are re-extracted with index-based loops that do not call the iterator (the S5 indexed candidates).

## PROPOSED-HM-C: core option result combinators

**Statement.** The gate definitions of Option::ok_or, Result::map_err, Result::map, the Try/FromResidual instances and the Option/Result equality instances are accepted as the standard Option/Result semantics.

**Members.** 21 entries, 7 distinct names in 15 gate modules. Reached by the deployed_splitB cone: 21 by a cone constant of the same short name, 19 by gate module. Reached by a CLOSED-row root module: 21. CLOSED rows touched (module or constant route, first 12 of 205): TX1:001, TX1:002, TX1:003, TX1:005, TX1:006, TX1:007, TX1:008, TX1:009, TX1:010, TX1:012, TX1:013, TX1:014.

**Names.** `alloc.collections.TryReserveError`; `core.option.Option.Insts.CoreCmpPartialEqOption.eq`; `core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual`; `core.option.Option.Insts.CoreOpsTry_traitTry.branch`; `core.option.Option.ok_or`; `core.result.Result.map`; `core.result.Result.map_err`

**Pinned crate and version.** Rust alloc library, rustc nightly-2026-06-01 sysroot (tool pin PCQ_*_PINS.json; no crate version) (others: see JSON)

**Consumers.** gate modules: AspisR1Post25SamplerIndexedAddSmallCandidate.Funs, AspisR1PrefixAggregateParser.Funs, AspisR1TerminalDecoder.Funs, AspisR72Sampler.Funs, NFY_Part043, NHI_FilledExtracted, NHI_FilledTypes, NID_ResumeEmissionFuns, NMT_first.Funs, NMT_stage1_owned.Funs, R1CandidateFieldParsers, RPu_FIq_NativeExternal, RPz7_FIo_NativeFuns, RPz7_FIo_NativeTypes ....

**Removal condition.** Remove when proved equal to the Aeneas library definitions by one generic lemma per combinator (they are small and closed); this is a proof task, not a cryptographic assumption.

## PROPOSED-HM-D: core array slice ops

**Statement.** The gate definitions of core array and slice operations (Array::map, array equality against slices, from_fn, slice indexing helpers) are accepted as the std semantics.

**Members.** 9 entries, 6 distinct names in 7 gate modules. Reached by the deployed_splitB cone: 5 by a cone constant of the same short name, 9 by gate module. Reached by a CLOSED-row root module: 9. CLOSED rows touched (module or constant route, first 12 of 128): TX1:016, TX1:017, TX1:020, TX1:029, TX1:030, TX1:035, TX1:045, TX1:046, TX1:049, TX1:050, TX1:051, TX1:052.

**Names.** `FIq_Native.core.array.Array.map`; `Slice.Insts.CoreCmpPartialEqArray.eq`; `Slice.Insts.CoreCmpPartialEqArray.ne`; `core.array.Array.map`; `core.array.from_fn`; `core.slice.Slice.windows`

**Pinned crate and version.** Rust std/core, toolchain-pinned (others: see JSON)

**Consumers.** gate modules: NFN_ExtractedGeometry, NFY_Part042, NID_ResumeEmissionFuns, NJA_CountBody, NMT_stage1_owned.Funs, RPu_FIq_Native08, RPu_FIq_NativeExternal.

**Removal condition.** Remove by a generic Lean lemma per operation against the Aeneas library, or by re-extraction without the operation.

## PROPOSED-HM-E: alloc and allocator models

**Statement.** The gate definitions of alloc::collections::TryReserveError, Vec::try_reserve_exact, String clone and the explicit allocator interpretation (FIo_Native.Allocation instance-implicit binder) are accepted as the allocation behaviour; every equality theorem holds for every allocator instance.

**Members.** 5 entries, 3 distinct names in 4 gate modules. Reached by the deployed_splitB cone: 3 by a cone constant of the same short name, 2 by gate module. Reached by a CLOSED-row root module: 5. CLOSED rows touched (module or constant route, first 12 of 73): TX1:001, TX1:002, TX1:005, TX1:006, TX1:007, TX1:008, TX1:010, TX1:012, TX1:013, TX1:014, TX1:016, TX1:017.

**Names.** `FIo_Native.Allocation (instance-implicit parameter)`; `alloc.string.String.Insts.CoreCloneClone.clone`; `alloc.vec.Vec.try_reserve_exact`

**Pinned crate and version.** Rust alloc library, rustc nightly-2026-06-01 sysroot (tool pin PCQ_*_PINS.json; no crate version) (others: see JSON)

**Consumers.** gate modules: NHI_FilledExtracted, NHJ_SnapshotReference.Funs, RPz7_FIo_NativeFuns, RPz7_FIo_NativeTypes.

**Removal condition.** Owned by the Stream A final trust audit (allocator/borrow item); this class only records which gate modules carry the binder. Remove when the allocator interpretation is discharged or the consumers are shown allocation-free.

## PROPOSED-HM-F: core num ops iter models

**Statement.** The gate definitions of core::num integer helpers (count_ones, trailing_zeros and their lemmas), core::ops::range clone, Rev/RangeInclusive folds (revFold, rangeFold, range_clone_usize) are accepted as the std semantics.

**Members.** 16 entries, 16 distinct names in 2 gate modules. Reached by the deployed_splitB cone: 11 by a cone constant of the same short name, 16 by gate module. Reached by a CLOSED-row root module: 16. CLOSED rows touched (module or constant route, first 12 of 67): TX1:081, TX1:082, TX1:083, TX1:087, TX1:094, TX1:122, TX1:128, TX1:136, TX1:137, TX1:168, TX1:169, TX1:170.

**Names.** `core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold`; `core.iter.traits.iterator.Iterator.all.default`; `core.num.U16.count_ones`; `core.num.U16.count_ones_aux`; `core.num.U16.count_ones_aux_le`; `core.num.U16.count_ones_nat`; `core.num.U16.count_ones_nat_le`; `core.num.U16.trailing_zeros`; `core.num.U16.trailing_zeros_aux_le`; `core.num.U16.trailing_zeros_nat`; `core.num.U16.trailing_zeros_nat_le`; `core.ops.range.Range.Insts.CoreCloneClone.clone`; `core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.fold`; `rangeFold`; `range_clone_usize`; `revFold`

**Pinned crate and version.** Rust std/core, toolchain-pinned (others: see JSON)

**Consumers.** gate modules: NJA_CountBody, RPu_FIq_NativeExternal.

**Removal condition.** Remove by proving each against the Lean integer library, or by re-extraction through Aeneas library definitions.

## PROPOSED-HM-G: aeneas discriminant helpers

**Statement.** The read_discriminant functions and the ImportUnionNamedDiscriminant registration are accepted as the discriminant reading of the corresponding Rust enums (P4b/P4c classified these as post-processing items).

**Members.** 7 entries, 7 distinct names in 3 gate modules. Reached by the deployed_splitB cone: 1 by a cone constant of the same short name, 6 by gate module. Reached by a CLOSED-row root module: 7. CLOSED rows touched (module or constant route, first 12 of 95): TX1:017, TX1:020, TX1:029, TX1:030, TX1:035, TX1:038, TX1:045, TX1:046, TX1:049, TX1:050, TX1:051, TX1:052.

**Names.** `import_union_discriminant (registration attribute) / ImportUnionNamedDiscriminant`; `pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.read_discriminant`; `pool_v1.pair_forest_semantic_terminal.CompiledVariant.read_discriminant`; `pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.read_discriminant`; `pool_v1.pair_forest_semantic_terminal.r0.Public.read_discriminant`; `state_only_prefix.r0.Error.read_discriminant`; `transport.Variant discriminant instance (NEV_discriminantVariant)`

**Pinned crate and version.** aspis-r1-cost-probe transport::Variant (isolated copy, frozen tree) (others: see JSON)

**Consumers.** gate modules: NEV_AccumulateRaw.Types, NGD_AtG.Types, RPu_FIq_NativeTypes.

**Removal condition.** Remove by a proof that each read_discriminant equals the match-based discriminant of the extracted enum, or by emitting the Aeneas-native form.

## PROPOSED-HM-I: frozen crate item models and gate side adaptations

**Statement.** Gate definitions that are not Aeneas output but replace or adapt a frozen-crate function or type (aspis_core field/wide_exact/transport items, atomic_statement.encode_digest_canonical, pool_v1.* decoders, fast_pairing, verifier/BatchedWeights items, AdapterRw.Ops) are accepted as models of the frozen functions of aspis-core 0.1.0, aspis-statement 0.1.0 and aspis-r1-cost-probe 0.1.0 (workspace members of 4bb3b3f).

**Members.** 122 entries, 71 distinct names in 29 gate modules. Reached by the deployed_splitB cone: 105 by a cone constant of the same short name, 104 by gate module. Reached by a CLOSED-row root module: 104. CLOSED rows touched (module or constant route, first 12 of 367): TX1:001, TX1:002, TX1:003, TX1:004, TX1:005, TX1:006, TX1:007, TX1:008, TX1:009, TX1:010, TX1:011, TX1:012.

**Names.** `AdapterRw.Ops`; `AspisR1CircleFallback.circle.secure_ood_circle_point_from_parameter`; `BatchedWeights.push`; `aspis_core.circle.SecureCirclePoint`; `aspis_core.digest.Digest32`; `aspis_core.field.CM31`; `aspis_core.field.CM31.mul`; `aspis_core.field.M31`; `aspis_core.field.M31.ONE`; `aspis_core.field.M31.ZERO`; `aspis_core.field.M31.double`; `aspis_core.field.M31.from_le_bytes`; `aspis_core.field.M31.mul`; `aspis_core.field.M31.reduce_u64`; `aspis_core.field.M31.sub`; `aspis_core.field.M31.to_le_bytes`; `aspis_core.field.P`; `aspis_core.field.QM31`; `aspis_core.field.QM31.Insts.CoreCloneClone.clone`; `aspis_core.field.QM31.ZERO`; `aspis_core.field.QM31.add`; `aspis_core.field.QM31.from_le_bytes`; `aspis_core.field.QM31.mul`; `aspis_core.field.QM31.write_le_bytes`; `aspis_core.field.wide_exact.WideExact`; `aspis_core.field.wide_exact.WideExact.ZERO`; `aspis_core.field.wide_exact.WideExact.add`; `aspis_core.field.wide_exact.WideExact.from_le_bytes`; `aspis_core.field.wide_exact.WideExact.from_qm31`; `aspis_core.field.wide_exact.WideExact.mul_qm31`; `aspis_core.field.wide_exact.WideExact.to_le_bytes`; `aspis_core.field.wide_exact.WideExact.to_limbs`; `aspis_core.r0.heap.filled`; `aspis_core.r0.merkle.parent_with_digest`; `aspis_core.r0.transport.COEFFICIENT_TO_ROW`; `atomic_statement.encode_digest_canonical`; `fast_pairing.canonical.Dot.push`; `field.CM31`; `field.M31`; `field.QM31`; and 31 more (see the JSON)

**Pinned crate and version.** aspis-core (workspace member of the frozen tree 4bb3b3f) (others: see JSON)

**Consumers.** gate modules: AdapterRwModel, AspisR1PrefixAggregateParser.Funs, AspisR1SemanticCallExtraction.Funs, AspisR1TerminalDecoder.Funs, AspisR72Sampler.Funs, AspisV8R19.ComplexFieldSlice, AspisV8R19.GuardedFieldSlice, AspisV8R19.QuarticFieldSlice, CurrentCompactCallerModelV1, FinishCandidateExplicitOps, LoopPowersCandidateModel, NEV_AccumulateRaw.Types / NFS_AccumPart00, NFY_Part043, NID_ResumeEmissionFuns ....

**Removal condition.** Remove per definition by a P1 frozen extraction plus a Lean equality (the P2 pass); each such entry that is proved becomes AENEAS-equivalent and leaves the list. The record is large because several gate modules are hand-transformed copies of frozen sources (the 24 no-source cut modules, see PCXF_NOSOURCE.md).

## PROPOSED-HM-J: proof structure or toolchain adaptations

**Statement.** Proof-structure entries (the H_P hypothesis, NNG_call/NMP_call arrays) recorded as hand-model items by P2/P3 jobs.

**Members.** 2 entries, 2 distinct names in 2 gate modules. Reached by the deployed_splitB cone: 0 by a cone constant of the same short name, 0 by gate module. Reached by a CLOSED-row root module: 0. CLOSED rows touched (module or constant route, first 12 of 0): .

**Names.** `H_P: PRVFresh_TD.aspis_core.field.P := ok gate.P`; `NNG_call_0..15 / NMP_call_0..11`

**Pinned crate and version.** not determined by the source job

**Consumers.** gate modules: NNG_verify_finish, NMP_prepare, PRVEq_AspisR1TerminalDecoder_FunsLoop_P3.lean.

**Removal condition.** Not trust: H_P was discharged in P2f (PCUF-C5); the call arrays are parameters of the cited theorems.

## PROPOSED-HM-K: other

**Statement.** Hand-written gate definitions not matched by any class pattern (listed by name in PCXF_HAND_MODELS.json).

**Members.** 32 entries, 31 distinct names in 11 gate modules. Reached by the deployed_splitB cone: 22 by a cone constant of the same short name, 28 by gate module. Reached by a CLOSED-row root module: 30. CLOSED rows touched (module or constant route, first 12 of 147): TX1:003, TX1:011, TX1:017, TX1:020, TX1:026, TX1:029, TX1:030, TX1:035, TX1:045, TX1:046, TX1:049, TX1:050.

**Names.** `Discriminant (Option T) Isize (local instance optionDiscriminant)`; `Types.lean adaptation (ImportUnionNamedDiscriminant)`; `aspis_r1_cost_probe.transport.Variant`; `aspis_r1_cost_probe.transport.Variant.tag`; `aspis_r1_cost_probe.verifier.PROOF_BYTES`; `aspis_r1_cost_probe.verifier.Prepared`; `aspis_r1_cost_probe.verifier.candidate.tx1`; `aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common`; `aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public`; `aspis_statement.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1`; `aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1`; `aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES`; `aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1`; `block`; `error`; `first_decoded`; `multiproof.binary_parent`; `multiproof.generate`; `multiproof.sort_dedup`; `multiproof.verify`; `r1_pool_adapter.decode_public_statement_box`; `r1_pool_adapter.owned.require_distinct_accounts`; `r1_pool_adapter.owned.require_readonly_buffer`; `r1_pool_adapter.owned.require_verifier_checkpoint`; `r1_pool_adapter.owned.require_zero`; `r1_semantic.semantic_boundary`; `sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once`; `scalar`; `solana_sha256_hasher.hashv`; `weights`; `weights.powers`

**Pinned crate and version.** Rust std (core/alloc) at the nightly-2026-09-17 sysroot of the pinned Charon; not a crates.io package (core::option::Option residual); tools/s8-kani-20261021 crate (others: see JSON)

**Consumers.** gate modules: AspisR1SemanticCallExtraction.Funs, NGT_Emitted, NID_ResumeEmissionFuns, NJA_CountBody, NMT_first.Funs, NMT_stage1_owned.Funs, Port5Q2_ReaderWeights, RPz7_AspisR1CircleSampleWrapper_Funs, RPz7_WAdm_Fissioned_Types, S8OwnedP6.Funs, S8OwnedP6.Types.

**Removal condition.** Classify per entry before any trust row is considered.

## Unresolved externals (not a trust proposal)

601 entries name an external of a fresh emission for which no gate definition was found in the examined gate files (the fresh file elaborates only if the compiled gate environment supplies the name). These are provenance obligations: until each is resolved to an Aeneas library definition or a hand model, the equalities that depend on it are conditional on the gate constant of that name. Most are Aeneas-library items (core/alloc) that the gate environment provides through imported Aeneas modules. See `proved_definitions_conditional_on_it` in PCUF_HAND_MODELS.json for the 22 proved definitions that depend on one.

## Cross-class notes

* The L187 closure and the gate environment already contain these names; whether the owner treats class (c) to (g) as std-library trust or as proof tasks is an owner decision. This job recommends treating (c), (d), (f), (g) as proof tasks (small, closed, generic lemmas) and (a), (b), (e), (h), (i) as trust rows only until their removal conditions are met.
* S1ValuesOwnedModelV1 is in the deployed_splitB cone (module-level hit, 7 CLOSED rows) and its link to the frozen function is an unproved P3 obligation; do not treat it as an unused template.

## Classes added by the second P6 run (PROPOSED text only)

### PROPOSED-HM-L: ShrAmt bridge

**Statement.** ShrAmt bridge: verified against Rust semantics and the pinned translation, NPE_ 2026-11-10 (overflow-checks-off only; never reuse for checked shifts with amounts wider than 32 bits)

**Residuals.** Not checked against an SBF-target build (the runtime tests were x86_64). Relies on Lean's usize width equalling the target's, which every gate module already shares. In CHECKED mode the bridge is NOT faithful for usize amounts >= 2^32 and must never be used there.

**Removal condition.** None needed for the overflow-checks-OFF use; the item is a verified bridge and could be recorded as discharged. It must carry the restriction "never reuse for checked shifts with amounts wider than 32 bits".

### PROPOSED-HM-M: array_from_fn_copy standing in for core::array::from_fn

**Statement.** The gate hand model array_from_fn_copy is accepted as the semantics of core::array::from_fn (pinned Rust core library) for the instantiations the 23 blocked dependants use. **Removal.** one bridge theorem per (element type, closure) instantiation, or re-extraction through a library definition. Owner decides; the dependants stay OPEN until then.

### PROPOSED-HM-N: parametric records (Port3_NativeGeometryBody Ops, Port4C_NativePrefix Leaves, Port5Q2_ReaderWeights ReadK/IterMut model, AdapterRwModel AdapterRw.Ops) and compact.OFF_* constants

**Statement.** The hand-written records are accepted as the boundary through which the gate functions reach field, domain, reader and SDK operations; the frozen functions call the concrete items. **Removal.** instantiate the record by the frozen items and prove the fresh = gate equality for the instantiation (34 definitions HAND_ADAPTED); compact.OFF_* requires the Ops-instance constants to be shown equal to the frozen constants.

### PROPOSED-HM-O: cross-crate constant encoding assumption (one line)

A fresh external axiom of type Result X for a cross-crate constant is linked to a transparent value (ok <gate value>, or by name to the gate constant); the link between the Aeneas external axiom and the transparent value is itself an encoding assumption, proved only for M31.ZERO/ONE and QM31.ZERO/ONE (PRVEq_const_bind, PCUH_L035/L037) and open for the rest (state_only_hiding STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS, Native07 selected_claim, Native13 COPY_PATTERNS literal, parametric transports).

### Externals with no gate definition: {'a_resolved_by_gate_hand_model_or_constant': 502, 'b_covered_by_existing_trust_row': 0, 'c_genuinely_unresolved': 99}

No existing trust row of the 2026-10-27 appendix literally covers any of the 601 (class b is empty); the appendix SDK rows are account-data/RefCell borrow fields, not the Pubkey/Hash type models; TrustedStd covers only option_ok_or and result_unwrap32. (c) is an upper bound (see PCXF_EXTERNALS.json rule).


## Delta against PCXE_TRUST_PROPOSALS.md

No hand model was added by P1i, P3f-P3l (their HAND_MODELS files add none; PCVK_ lists proof-internal lemmas and a tactic). The class texts above are unchanged. Rows are now named on records (PCXF_TRUST_NAMING.json): HM-B on 6 definitions (4 WideToBytes, 2 Port23PUSH), CrossCrateConstantEncoding on 1, HM-C on 6 PublicPreparation definitions and ReviewedTranscription-PublicPreparation.public_bytes on 3 of them (outside the headline cone constants). HM-A is named on CONDITIONAL records of AdapterRw, NMT and the caller models as a further dependency. Open wording items: HM-A text does not name solana_sdk_ids bpf_loader_upgradeable.id; no row names derive(PartialEq) on Aspis types (two P1i records stay OPEN for that); HM-G may be an Aspis-side proof item (PCVG_ note); the Rust sysroot string of the pins (nightly-2026-06-01 vs 2026-09-17, client 1.94.1) must be confirmed before a row is entered. Rows are proposals; none entered.
