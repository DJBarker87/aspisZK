# Formatter dependency closure — Stage 0

Candidate revision `af96787aa3`; branch `codex/cx-prover-dict-20261026`.

**Result:** no audited candidate declaration depends on `Aeneas.Std.core.fmt.Formatter`. This is an axiom-dependency result, not native Formatter adequacy or a deployed privacy conclusion.

## Exact scope

Union of selected dictionary closure, explicit P6 body root, deployed headline, and five CB3 source roots. Does not assert that currently unjoined dictionary/CB roots are instantiated into the headline.

Audited 321 selected family modules in 1188 source modules. Every declaration owned by a reachable `PDict_`, `ProverRw*`, `PV_CB_*`, or `PV_CB3_*` module was passed to the actual `#print axioms` elaborator, including private/generated declarations. All 28 `ExternalTypes.op0`–`op27` projections were also printed. Definitions of the installed representations and their installation theorems are included, including the conditional Error3/Formatter27 reference carriers.

`ProverRwFull.ExternalFuns` and `R1Z.ProverRwP6BodyData.refinement_of_data` were printed explicitly. The eight import roots and every source/object hash are in `closure-input.json` and `26201/26201-input.json`. Some modules contain audit commands only and own zero declarations. This is a focused cached audit, not a coherent frozen release rebuild.

## Axiom identity and import inventory

`Aeneas.Std.core.fmt.Formatter : Type` is declared by `Aeneas.Std.Core.Fmt` (retained exact source: `Fmt.lean.txt`). Its diagnostic `#print axioms` correctly reports `[Aeneas.Std.core.fmt.Formatter]`. It is distinct from the candidate alias `ProverRwFull.core.fmt.Formatter`, which is external type slot 27.

729 project modules transitively import the backend module. Every importing module and a complete witness import path is in `formatter-importers.json` and the appendix below. Importing that module does not make a declaration depend on its axiom. **Candidate declarations with this axiom: none. Candidate modules owning such declarations: none.**

## Before/after axiom table

| Target | Before (J26201) | After Stage 0 |
|---|---|---|
| Backend diagnostic `Aeneas.Std.core.fmt.Formatter` | forbidden axiom itself | unchanged; unselected |
| 12920 candidate/root/type-slot reports | subset of `propext`, `Classical.choice`, `Quot.sound` | unchanged; no dependency to eliminate |
| `ProverRwFull.ExternalFuns` | `propext, Classical.choice, Quot.sound` | unchanged |
| `ProverRwP6BodyData.refinement_of_data` | standard subset (full exact list in receipt) | unchanged |

| Attempt / target | Exit | Wall | Peak RSS KiB | Swaps | Revision | Axioms |
|---|---:|---|---:|---:|---|---|
| J26202 `R1Z/PDict_FormatterRoots262` | 1 | 0:01.98 | 4309320 | 0 | 41e05299e9 | nine standard-only reports; four unavailable-name errors |
| J26203 `R1Z/PDict_FormatterRoots262` | 0 | 0:01.76 | 4317144 | 0 | 41e05299e9 | nine standard-only/empty reports, including headline |

## Ledger disposition

**V269 and V270: CLOSED-ON-CANDIDATE for the lead-requested Formatter RELEASE BLOCKER only.** Exact statement: “At the pinned candidate sources/objects inventoried here, every audited candidate declaration, all 28 external type-slot projections, ExternalFuns and the P6 refinement root have axiom closure contained in `{propext, Classical.choice, Quot.sound}`; none uses `Aeneas.Std.core.fmt.Formatter`.”

Before: both OPEN under recount 2; D203 did not justify native type27 reduction. After: the requested standard-axiom closure condition is checked on the candidate without replacing a type or proof. No quantifier, carrier, simulator, observer, hypothesis, conclusion, shipped source or backend changed. **The broader native type27 sink/value/options/failure/state association remains unproved and is not credited as removed. Native type count remains 26/28; source selection remains 175/255.** This scoped status must not be read as native adequacy or closure of V038.

## Route and existing symbolic obligations

Stage 0 clean-closure branch. No Stage 1 modification is necessary for the mechanical axiom target. Candidate source contains the split avoidance proofs: `PDict_FmtPublicationFrame.publication_frame` (namespace `R1Z.PDict_FmtErase`) factors publication before `erase_420`; `PDict_FmtRetryComplete.erase_425` uses `fixed_equal`. Those files exist on the candidate branch but are not imported by the selected dictionary closure; no audit credit is claimed for those unimported files. The stale failed `PDict_FmtErase26` source and these split successors are not imported by the selected closure. No large-term reduction was attempted.

## Receipts and budget

| Attempt / target | Exit | Wall | Peak RSS KiB | Swaps | Revision | Axioms |
|---|---:|---|---:|---:|---|---|
| J26200 `R1Z/PDict_FormatterClosure262` | 130 | 2:02.20 | 4359800 | 0 | af96787aa3 | no completed output; manually interrupted to replace repeated environment scans with one scan |
| J26201 `R1Z/PDict_FormatterClosure262` | 0 | 0:51.34 | 4407372 | 0 | af96787aa3 | 12920 standard-only candidate reports; one deliberate backend diagnostic |

J26200 is charged. J26201 changed the audit algorithm, not proof declarations. Caps: Lean -M7000, MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax128 through the unchanged shared launcher. One scope at a time. Raw stdout, GNU time, SHA, dependency fingerprint and full axiom reports are retained per attempt. Admission logs are retained separately. No Kani invocation had run at Stage 0 completion; Stage 2 is recorded separately in `STAGE2.md`.

J26203 completes the focused explicit endpoint check: all nine reports are standard-only or empty, including `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed`. J26202 was rejected solely for four unimported older symbolic-route names; those names were removed, no proof changed. All 321 family source hashes match this worktree (213) or the pinned read-only sibling git revisions (108), with zero mismatches; see `worktree-source-binding.json`. Target not yet established.

## Candidate family modules

| Module | Audited declarations | Backend Formatter module imported |
|---|---:|---|
| `R1Z.PDict_Advance244` | 4 | yes |
| `R1Z.PDict_Array32` | 7 | yes |
| `R1Z.PDict_ArrayReference244` | 14 | yes |
| `R1Z.PDict_Audit231` | 0 | yes |
| `R1Z.PDict_CarrierInstall` | 8 | yes |
| `R1Z.PDict_CarriersSource` | 299 | yes |
| `R1Z.PDict_CodecDictionary` | 5 | yes |
| `R1Z.PDict_CodecSource` | 44 | yes |
| `R1Z.PDict_Compare` | 9 | yes |
| `R1Z.PDict_ConstantsSource` | 42 | yes |
| `R1Z.PDict_CopyCell244` | 5 | yes |
| `R1Z.PDict_CopyCorrect244` | 4 | yes |
| `R1Z.PDict_CopySource244` | 9 | yes |
| `R1Z.PDict_CryptoTypesSource` | 122 | yes |
| `R1Z.PDict_CtConstructor` | 5 | yes |
| `R1Z.PDict_CtUpdate` | 4 | yes |
| `R1Z.PDict_DigestDelegates` | 6 | yes |
| `R1Z.PDict_DigestNew` | 1 | yes |
| `R1Z.PDict_ErrorCarrier` | 25 | yes |
| `R1Z.PDict_ErrorKind` | 142 | yes |
| `R1Z.PDict_EventReplay244` | 19 | no |
| `R1Z.PDict_EventWorld244` | 49 | no |
| `R1Z.PDict_Fence` | 8 | yes |
| `R1Z.PDict_FileCarrier` | 13 | yes |
| `R1Z.PDict_FileFlush` | 6 | yes |
| `R1Z.PDict_FileWorld244` | 4 | yes |
| `R1Z.PDict_FinalDictionary` | 85 | yes |
| `R1Z.PDict_FormatterQuotient244` | 13 | yes |
| `R1Z.PDict_IOCarriers` | 7 | yes |
| `R1Z.PDict_Installed` | 77 | yes |
| `R1Z.PDict_MaskError` | 17 | yes |
| `R1Z.PDict_MoreCarriers` | 16 | yes |
| `R1Z.PDict_Numeric` | 44 | yes |
| `R1Z.PDict_OSRegression244` | 6 | no |
| `R1Z.PDict_OffpathBorrow` | 6 | yes |
| `R1Z.PDict_Options` | 13 | yes |
| `R1Z.PDict_Ordering` | 8 | yes |
| `R1Z.PDict_OwnedSource244` | 106 | yes |
| `R1Z.PDict_PathRefSource` | 2 | yes |
| `R1Z.PDict_PathTypesSource` | 120 | yes |
| `R1Z.PDict_Primitives` | 9 | yes |
| `R1Z.PDict_Publication` | 13 | yes |
| `R1Z.PDict_PureDictionary` | 13 | yes |
| `R1Z.PDict_PureSource` | 11 | yes |
| `R1Z.PDict_RejectionStd` | 9 | yes |
| `R1Z.PDict_RejectionStdSource` | 12 | yes |
| `R1Z.PDict_RemainingCaller231` | 2 | yes |
| `R1Z.PDict_RemainingCommute231_01` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_02` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_03` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_04` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_05` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_06` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_07` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_08` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_09` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_10` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_11` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_12` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_13` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_14` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_15` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_16` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_17` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_18` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_19` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_20` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_21` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_22` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_23` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_24` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_25` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_26` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_27` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_28` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_29` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_30` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_31` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_32` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_33` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_34` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_35` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_36` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_37` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_38` | 1 | yes |
| `R1Z.PDict_RemainingCommute231_39` | 1 | yes |
| `R1Z.PDict_RemainingDictionary231` | 5 | yes |
| `R1Z.PDict_RemainingExt231` | 2 | yes |
| `R1Z.PDict_RemainingLeafSource` | 5 | yes |
| `R1Z.PDict_RemainingValues231` | 3 | yes |
| `R1Z.PDict_ReserveErrorSource` | 36 | yes |
| `R1Z.PDict_ResumeDictionary` | 93 | yes |
| `R1Z.PDict_RetryCap` | 19 | yes |
| `R1Z.PDict_RowBounds244` | 1 | yes |
| `R1Z.PDict_RowChunk244_0` | 294 | yes |
| `R1Z.PDict_RowChunk244_1` | 294 | yes |
| `R1Z.PDict_RowChunk244_2` | 294 | yes |
| `R1Z.PDict_RowChunk244_3` | 294 | yes |
| `R1Z.PDict_RowChunk244_4` | 294 | yes |
| `R1Z.PDict_RowChunk244_5` | 294 | yes |
| `R1Z.PDict_RowChunk244_6` | 294 | yes |
| `R1Z.PDict_RowChunk244_7` | 294 | yes |
| `R1Z.PDict_RowTable244` | 11 | yes |
| `R1Z.PDict_SHAConstructorSource` | 28 | yes |
| `R1Z.PDict_SaltClear` | 7 | yes |
| `R1Z.PDict_SinkCore244` | 45 | no |
| `R1Z.PDict_StatementTypesSource` | 325 | yes |
| `R1Z.PDict_TapeCells244` | 7 | yes |
| `R1Z.PDict_TapeCore244` | 43 | no |
| `R1Z.PDict_TapeCorrect244` | 4 | yes |
| `R1Z.PDict_TapeSource244` | 63 | yes |
| `R1Z.PDict_TapeSuffix244` | 4 | no |
| `R1Z.PDict_TapeTrace244` | 19 | no |
| `R1Z.PDict_TapeView244` | 16 | yes |
| `R1Z.PDict_Typenum` | 50 | yes |
| `R1Z.PDict_UIntOps` | 13 | yes |
| `R1Z.PDict_UIntSource` | 17 | yes |
| `R1Z.PDict_VolatileCell` | 5 | yes |
| `R1Z.PDict_WireError` | 74 | yes |
| `R1Z.PDict_World244` | 145 | yes |
| `R1Z.PV_CB3_Afterstate` | 21 | yes |
| `R1Z.PV_CB3_Op225Source` | 10 | yes |
| `R1Z.PV_CB3_Op229Source` | 15 | yes |
| `R1Z.PV_CB3_Op246Source` | 12 | yes |
| `R1Z.PV_CB3_PoleRows` | 15 | no |
| `R1Z.ProverRwBodyCandidateData` | 5 | yes |
| `R1Z.ProverRwBodyCandidateStore` | 3 | yes |
| `R1Z.ProverRwBodyDataCriterion` | 4 | yes |
| `R1Z.ProverRwBodyErrorData` | 8 | yes |
| `R1Z.ProverRwBodyNativeWideInstall` | 5 | yes |
| `R1Z.ProverRwBodyReservationTransport` | 7 | yes |
| `R1Z.ProverRwBodyStore` | 33 | yes |
| `R1Z.ProverRwBodyStoreSource` | 17 | yes |
| `R1Z.ProverRwCallerBinding` | 24 | yes |
| `R1Z.ProverRwDictionaryBaseField` | 5 | yes |
| `R1Z.ProverRwDictionaryBytes` | 11 | yes |
| `R1Z.ProverRwDictionaryBytesSource` | 46 | yes |
| `R1Z.ProverRwDictionaryConstants` | 9 | yes |
| `R1Z.ProverRwDictionaryDerived` | 13 | yes |
| `R1Z.ProverRwDictionaryDerivedSource` | 4 | yes |
| `R1Z.ProverRwDictionaryDigest` | 3 | yes |
| `R1Z.ProverRwDictionaryDomain` | 8 | yes |
| `R1Z.ProverRwDictionaryEmbedding` | 12 | yes |
| `R1Z.ProverRwDictionaryLayout` | 9 | yes |
| `R1Z.ProverRwDictionaryLayoutSource` | 52 | yes |
| `R1Z.ProverRwDictionaryMerkle` | 9 | yes |
| `R1Z.ProverRwDictionaryOption` | 12 | yes |
| `R1Z.ProverRwDictionaryOptionSource` | 7 | yes |
| `R1Z.ProverRwDictionaryScalar` | 34 | yes |
| `R1Z.ProverRwDictionaryTower` | 37 | yes |
| `R1Z.ProverRwDictionaryWideQM` | 4 | yes |
| `R1Z.ProverRwEntropyIteration` | 19 | yes |
| `R1Z.ProverRwEntropyObstruction` | 10 | yes |
| `R1Z.ProverRwFullExternalFuns` | 535 | yes |
| `R1Z.ProverRwFullExternalTypes` | 110 | yes |
| `R1Z.ProverRwFullFuns` | 1325 | yes |
| `R1Z.ProverRwFullSampler` | 13 | yes |
| `R1Z.ProverRwFullTypes` | 2016 | yes |
| `R1Z.ProverRwOuterAfterChecks` | 6 | yes |
| `R1Z.ProverRwOuterBytes` | 15 | yes |
| `R1Z.ProverRwOuterCaller` | 10 | yes |
| `R1Z.ProverRwOuterContext` | 25 | yes |
| `R1Z.ProverRwOuterContextModel` | 12 | yes |
| `R1Z.ProverRwOuterEncode` | 16 | yes |
| `R1Z.ProverRwOuterFrames` | 37 | yes |
| `R1Z.ProverRwOuterGuardBridge` | 8 | yes |
| `R1Z.ProverRwOuterGuardLeaves` | 9 | yes |
| `R1Z.ProverRwOuterInstalled` | 2 | yes |
| `R1Z.ProverRwOuterMapErr` | 5 | yes |
| `R1Z.ProverRwOuterPrefix` | 36 | yes |
| `R1Z.ProverRwOuterPrepare` | 27 | yes |
| `R1Z.ProverRwOuterTag` | 13 | yes |
| `R1Z.ProverRwOuterWrite` | 5 | yes |
| `R1Z.ProverRwP6ArrayMap` | 10 | yes |
| `R1Z.ProverRwP6ArrayMutRead` | 1 | yes |
| `R1Z.ProverRwP6ArrayRead` | 4 | yes |
| `R1Z.ProverRwP6BaseTotal` | 5 | yes |
| `R1Z.ProverRwP6BindTotal` | 1 | yes |
| `R1Z.ProverRwP6BodyCandidate` | 6 | yes |
| `R1Z.ProverRwP6BodyData` | 2 | yes |
| `R1Z.ProverRwP6BodyGamma` | 2 | yes |
| `R1Z.ProverRwP6BodyGammaPort` | 8 | yes |
| `R1Z.ProverRwP6BodyStore` | 5 | yes |
| `R1Z.ProverRwP6BoundaryInstall` | 4 | yes |
| `R1Z.ProverRwP6BoundaryReduce` | 1 | yes |
| `R1Z.ProverRwP6BoundarySource` | 53 | yes |
| `R1Z.ProverRwP6BoundaryStep` | 5 | yes |
| `R1Z.ProverRwP6BoundaryTotal` | 1 | yes |
| `R1Z.ProverRwP6ComplexTotal` | 5 | yes |
| `R1Z.ProverRwP6FlatInstall` | 3 | yes |
| `R1Z.ProverRwP6FlatSource` | 13 | yes |
| `R1Z.ProverRwP6FlatTotal` | 1 | yes |
| `R1Z.ProverRwP6PowersCongruence` | 7 | yes |
| `R1Z.ProverRwP6PowersControl` | 10 | yes |
| `R1Z.ProverRwP6PowersCoordinates` | 2 | yes |
| `R1Z.ProverRwP6PowersFinite` | 20 | yes |
| `R1Z.ProverRwP6PowersGammaSource` | 2 | yes |
| `R1Z.ProverRwP6PowersGammaValues` | 3 | yes |
| `R1Z.ProverRwP6PowersInstall` | 4 | yes |
| `R1Z.ProverRwP6PowersNativeBridge` | 21 | yes |
| `R1Z.ProverRwP6PowersNativeCaller` | 3 | yes |
| `R1Z.ProverRwP6PowersNativeFactor` | 6 | yes |
| `R1Z.ProverRwP6PowersNativeStep` | 12 | yes |
| `R1Z.ProverRwP6PowersRunTotal` | 5 | yes |
| `R1Z.ProverRwP6PowersSelectedTotal` | 5 | yes |
| `R1Z.ProverRwP6PowersSource` | 10 | yes |
| `R1Z.ProverRwP6PowersTotal` | 6 | yes |
| `R1Z.ProverRwP6QuarticTotal` | 6 | yes |
| `R1Z.ProverRwP6ResultMap` | 4 | yes |
| `R1Z.ProverRwP6TransitionInstall` | 5 | yes |
| `R1Z.ProverRwP6TransitionSource` | 120 | yes |
| `R1Z.ProverRwP6TransitionTransport` | 12 | yes |
| `R1Z.ProverRwP6WideDecode` | 6 | yes |
| `R1Z.ProverRwP6WideTotal` | 5 | yes |
| `R1Z.ProverRwP7FibreSource` | 29 | yes |
| `R1Z.ProverRwP7ReverseSource` | 11 | yes |
| `R1Z.ProverRwP7TraceCloneInstall` | 6 | yes |
| `R1Z.ProverRwP7TraceCloneSource` | 4 | yes |
| `R1Z.ProverRwP7TraceCloneTotal` | 3 | yes |
| `R1Z.ProverRwQueryAttempt` | 74 | yes |
| `R1Z.ProverRwQueryBlock` | 7 | yes |
| `R1Z.ProverRwQueryCallerSplit` | 5 | yes |
| `R1Z.ProverRwQueryComplete` | 16 | yes |
| `R1Z.ProverRwQueryContains` | 24 | yes |
| `R1Z.ProverRwQueryDecode` | 6 | yes |
| `R1Z.ProverRwQueryExecution` | 26 | yes |
| `R1Z.ProverRwQueryFinishTransport` | 22 | yes |
| `R1Z.ProverRwQueryInstalled` | 4 | yes |
| `R1Z.ProverRwQueryListStep` | 11 | yes |
| `R1Z.ProverRwQueryMaterial` | 22 | yes |
| `R1Z.ProverRwQueryMaterialTransport` | 10 | yes |
| `R1Z.ProverRwQueryMembership` | 13 | yes |
| `R1Z.ProverRwQueryModelChain` | 10 | yes |
| `R1Z.ProverRwQueryNativeAttempt` | 36 | yes |
| `R1Z.ProverRwQueryOpening` | 35 | yes |
| `R1Z.ProverRwQueryPolicy` | 5 | yes |
| `R1Z.ProverRwQueryPublish` | 4 | yes |
| `R1Z.ProverRwQueryResult` | 9 | yes |
| `R1Z.ProverRwQueryRetry` | 24 | yes |
| `R1Z.ProverRwQueryScan` | 35 | yes |
| `R1Z.ProverRwQuerySemantics` | 27 | yes |
| `R1Z.ProverRwQuerySourceWindow` | 14 | yes |
| `R1Z.ProverRwQueryStop` | 5 | yes |
| `R1Z.ProverRwQueryTrace` | 24 | yes |
| `R1Z.ProverRwQueryTransition` | 14 | yes |
| `R1Z.ProverRwQueryWindow` | 29 | yes |
| `R1Z.ProverRwQueryWindowStop` | 6 | yes |
| `R1Z.ProverRwQueryWord` | 16 | yes |
| `R1Z.ProverRwQueryWordTotal` | 12 | yes |
| `R1Z.ProverRwRetryModel` | 86 | yes |
| `R1Z.ProverRwRngCallerComposition` | 2 | yes |
| `R1Z.ProverRwRngCallerControl` | 36 | yes |
| `R1Z.ProverRwRngCallerEmission` | 261 | yes |
| `R1Z.ProverRwRngCallerEntropy` | 16 | yes |
| `R1Z.ProverRwRngCallerEvents` | 3 | yes |
| `R1Z.ProverRwRngCallerReplay` | 41 | yes |
| `R1Z.ProverRwRngCallerStep` | 51 | yes |
| `R1Z.ProverRwRngControl` | 11 | yes |
| `R1Z.ProverRwRngEmission` | 154 | yes |
| `R1Z.ProverRwRngNativeBodyEmission` | 110 | yes |
| `R1Z.ProverRwRngNativeBodyLeaves` | 82 | yes |
| `R1Z.ProverRwRngNativeBodyTypes` | 636 | yes |
| `R1Z.ProverRwRngNonzero` | 18 | yes |
| `R1Z.ProverRwRngOwnerBridge` | 13 | yes |
| `R1Z.ProverRwRngOwnerCertificate` | 4 | yes |
| `R1Z.ProverRwRngOwnerDraw` | 10 | yes |
| `R1Z.ProverRwRngOwnerEmission` | 16 | yes |
| `R1Z.ProverRwRngOwnerEvents` | 23 | yes |
| `R1Z.ProverRwRngOwnerInduction` | 10 | yes |
| `R1Z.ProverRwRngOwnerInventory` | 38 | yes |
| `R1Z.ProverRwRngOwnerState` | 10 | yes |
| `R1Z.ProverRwRngOwnerStep` | 24 | yes |
| `R1Z.ProverRwRngTape` | 10 | yes |
| `R1Z.ProverRwRngTransportValidity` | 12 | yes |
| `R1Z.ProverRwSamplerArithmetic` | 8 | yes |
| `R1Z.ProverRwSamplerModel` | 12 | yes |
| `R1Z.ProverRwSamplerTransport` | 38 | yes |
| `R1Z.ProverRwSemanticSampler` | 4 | yes |
| `R1Z.ProverRwSuccessArithmeticTotal` | 16 | yes |
| `R1Z.ProverRwSuccessArrayFromFn` | 18 | yes |
| `R1Z.ProverRwSuccessBodyInterpretation` | 7 | yes |
| `R1Z.ProverRwSuccessBorrow` | 9 | yes |
| `R1Z.ProverRwSuccessByteEquality` | 2 | yes |
| `R1Z.ProverRwSuccessCoefficientsSource` | 22 | yes |
| `R1Z.ProverRwSuccessComplexInverseExact` | 10 | yes |
| `R1Z.ProverRwSuccessComplexOperations` | 7 | yes |
| `R1Z.ProverRwSuccessConstants` | 9 | yes |
| `R1Z.ProverRwSuccessCtReduce` | 3 | yes |
| `R1Z.ProverRwSuccessCtSubtract` | 6 | yes |
| `R1Z.ProverRwSuccessEquality` | 8 | yes |
| `R1Z.ProverRwSuccessErrorInstall` | 109 | yes |
| `R1Z.ProverRwSuccessErrorSource` | 2 | yes |
| `R1Z.ProverRwSuccessField` | 7 | yes |
| `R1Z.ProverRwSuccessGeneric` | 6 | yes |
| `R1Z.ProverRwSuccessHashes` | 20 | yes |
| `R1Z.ProverRwSuccessHeapInstall` | 3 | yes |
| `R1Z.ProverRwSuccessHeapSource` | 6 | yes |
| `R1Z.ProverRwSuccessInverseInstall` | 9 | yes |
| `R1Z.ProverRwSuccessInverseSource` | 28 | yes |
| `R1Z.ProverRwSuccessInverseTotal` | 20 | yes |
| `R1Z.ProverRwSuccessNativeInverseTransport` | 27 | yes |
| `R1Z.ProverRwSuccessNativeNegInstall` | 3 | yes |
| `R1Z.ProverRwSuccessNativeNormalize` | 13 | yes |
| `R1Z.ProverRwSuccessNativeNormalizeWord` | 6 | yes |
| `R1Z.ProverRwSuccessNativePorts` | 45 | yes |
| `R1Z.ProverRwSuccessNativeWideInstall` | 4 | yes |
| `R1Z.ProverRwSuccessNativeWideTransport` | 13 | yes |
| `R1Z.ProverRwSuccessOptions` | 16 | yes |
| `R1Z.ProverRwSuccessParser` | 7 | yes |
| `R1Z.ProverRwSuccessParserSource` | 11 | yes |
| `R1Z.ProverRwSuccessPhiSource` | 7 | yes |
| `R1Z.ProverRwSuccessPointsSource` | 17 | yes |
| `R1Z.ProverRwSuccessPowerExact` | 12 | yes |
| `R1Z.ProverRwSuccessPowerTotal` | 16 | yes |
| `R1Z.ProverRwSuccessQuarticInverseExact` | 13 | yes |
| `R1Z.ProverRwSuccessQuarticOperations` | 5 | yes |
| `R1Z.ProverRwSuccessScalarInverseExact` | 7 | yes |
| `R1Z.ProverRwSuccessVectors` | 12 | yes |
| `R1Z.ProverRwSuccessWideSource` | 11 | yes |
| `R1Z.ProverRwSuccessWireInstall` | 3 | yes |
| `R1Z.ProverRwSuccessWireSource` | 22 | yes |

## Every project importer of the Formatter module

- `AspisR1CircleCaller25.Funs`
- `AspisR1CircleCaller25.Types`
- `AspisR1CoinEffect27.Funs`
- `AspisR1CoinEffect27.Types`
- `AspisR1EffectCallers27.Funs`
- `AspisR1EffectCallers27.Types`
- `AspisR1GammaCaller.Types`
- `AspisR1Post25Sampler.Funs`
- `AspisR1Post25Sampler.Types`
- `AspisR1Post25SamplerIndexedAddSmallCandidate.Funs`
- `AspisR1Post25SamplerIndexedAddSmallCandidate.Types`
- `AspisR1ProducerChecked47.Funs`
- `AspisR1ProducerChecked47.Types`
- `AspisR1ProducerRelease47.Basis`
- `AspisR1ProducerRelease47.Batched48`
- `AspisR1ProducerRelease47.Funs`
- `AspisR1ProducerRelease47.Interpolate48`
- `AspisR1ProducerRelease47.Kernels49`
- `AspisR1ProducerRelease47.Opening48`
- `AspisR1ProducerRelease47.Pairs`
- `AspisR1ProducerRelease47.Powers48`
- `AspisR1ProducerRelease47.Samples49`
- `AspisR1ProducerRelease47.Types`
- `AspisR1ProducerRelease47.Weights49`
- `AspisR1ProverCommit.Funs`
- `AspisR1ProverCommit.FunsExternal`
- `AspisR1ProverCommit.Types`
- `AspisR1ProverCommit.TypesExternal`
- `AspisR1ProverCommitReference.Funs`
- `AspisR1ProverCommitReference.FunsExternal`
- `AspisR1ProverCommitReference.Types`
- `AspisR1ProverLeaf.Funs`
- `AspisR1ProverLeaf.Types`
- `AspisR1ProverMaterial14.Funs`
- `AspisR1ProverMaterial14.Types`
- `AspisR1ProverStep8.Funs`
- `AspisR1ProverStep8.Types`
- `AspisR1ProverStreams.Funs`
- `AspisR1ProverStreams.FunsExternal`
- `AspisR1ProverStreams.Types`
- `AspisR1ProverStreams.TypesExternal`
- `AspisR1PublicNonce41.Funs`
- `AspisR1PublicNonce41.Types`
- `AspisR1PublicPreparation.Funs`
- `AspisR1PublicPreparation.Types`
- `AspisR1PublicSerializer34.Funs`
- `AspisR1PublicSerializer34.Types`
- `AspisR1Qm31ArithmeticProbe.Funs`
- `AspisR1Qm31ArithmeticProbe.Types`
- `AspisR1Qm31SamplerIndex.Funs`
- `AspisR1Qm31SamplerIndex.Types`
- `AspisR1Retry34.Funs`
- `AspisR1Retry34.Types`
- `AspisR1SemanticInit28.Funs`
- `AspisR1SemanticInit28.FunsExternal`
- `AspisR1SemanticInit28.Types`
- `AspisR1SimControl21.Funs`
- `AspisR1SimControl21.Types`
- `AspisR1SimSemantic20.Funs`
- `AspisR1SimSemantic20.Types`
- `AspisR1SimulatorCoin18.Funs`
- `AspisR1SimulatorCoin18.Types`
- `AspisR1SimulatorInsert19.Funs`
- `AspisR1SimulatorInsert19.Types`
- `AspisR72Sampler.Funs`
- `AspisR72Sampler.Types`
- `AspisV8R19.SamplerWordBridge`
- `AspisV8R19.SamplerWordRead`
- `AspisV8R19.SqueezeOracleBridge`
- `AspisV8R19.SqueezeSourceExecution`
- `ExtractedCurrentCM31Mul`
- `ExtractedCurrentM31AddSub`
- `ExtractedCurrentQM31Equality`
- `ExtractedCurrentQM31Exact`
- `ExtractedCurrentQM31Mul`
- `ExtractedCurrentQM31Tower`
- `ExtractedCurrentReducer`
- `ExtractedCurrentReducerOps`
- `ExtractedCurrentTowerAdd`
- `ExtractedDigest32SamplerTransport`
- `ExtractedQM31SamplerBytes`
- `ExtractedQM31SamplerCarrier`
- `ExtractedQM31SamplerCorrect`
- `ExtractedQM31SamplerDigits`
- `ExtractedQM31SamplerDivision`
- `ExtractedQM31SamplerIndexedCandidate`
- `ExtractedQM31SamplerPass`
- `ExtractedQM31SamplerPassLoop`
- `GammaCallerDigitsModel`
- `GammaCallerExplicitHelpers`
- `GammaCallerRankModel`
- `GammaCandidateAddSmallHelpersRefine`
- `GammaCandidateDecodedFieldRank`
- `GammaCandidateLowQuotient`
- `GammaCandidateTotalityV14`
- `IndexedCandidateAddSmallGeneratedOneStepV1`
- `IndexedCandidateAddSmallLoopCanonicalV11`
- `IndexedCandidateAddSmallNatModelV1`
- `IndexedCandidateAddSmallWrapperNatModelV3`
- `IndexedCandidateDecode8RetainedBridgeV3`
- `IndexedCandidateGeneratedLoopBridgeV4`
- `IndexedCandidateOrdinaryRetainedBridgeV5`
- `IndexedCandidateOrdinarySampleBridgeV3`
- `IndexedCandidateOuterByteBridgeV13`
- `IndexedCandidateOuterByteOutputSuccessV5`
- `ProverRwSampler.Funs`
- `ProverRwSampler.Types`
- `Query31ConcreteWordsDriverChain`
- `Query31ExplicitListLoop`
- `Query31ExplicitScanBody`
- `Query31ExplicitScanConcreteSteps`
- `Query31ModelDriverChain`
- `Query31ModelScanCall`
- `Query31ScanTypesOnly`
- `Query31UnrolledDriverFirstStop`
- `QueryScanConcreteWordsDecoder`
- `R0Z.BlockRefine`
- `R0Z.BlockWritersExtracted`
- `R0Z.BuilderBlocksChain`
- `R0Z.BuilderBlocksCopy`
- `R0Z.BuilderBlocksModel`
- `R0Z.BuilderWitness`
- `R0Z.BuilderWitnessMerged`
- `R0Z.BuilderWitnessTrace`
- `R0Z.BuilderWitnessTree`
- `R0Z.NodeRefine`
- `R0Z.NoteSpongeModel`
- `R0Z.PoseidonCanon`
- `R0Z.PoseidonConstLift`
- `R0Z.PoseidonExtracted`
- `R0Z.PoseidonInternal`
- `R0Z.PoseidonRefine`
- `R0Z.PoseidonRounds`
- `R0Z.PoseidonTables`
- `R0Z.ReadBackRefine`
- `R0Z.SpongeModel`
- `R0Z.SpongeRefine`
- `R0Z.WriterRefineAuxBlock`
- `R0Z.WriterRefineMerge`
- `R0Z.WriterRefineOcc`
- `R0Z.WriterRefineOccRow`
- `R0Z.WriterRefinePath`
- `R0Z.WriterRefinePathBlock`
- `R0Z.WriterRefinePathModel`
- `R0Z.WriterRefineValue`
- `R0Z.WriterRefineValueBlock`
- `R0Z.WriterRefineValueModel`
- `R0Z.WritersExtracted`
- `R1J.PrivacySamplerSpend`
- `R1J.PrivacySamplerSpendBin`
- `R1J.SamplerLawSpend`
- `R1J.SpendWitnessMap`
- `R1SamplerBytePass`
- `R1SamplerByteWord`
- `R1SourceSamplerByteRank`
- `R1Z.BuilderAdmissionCanonical`
- `R1Z.BuilderAdmissionCommon`
- `R1Z.BuilderAdmissionExtracted`
- `R1Z.BuilderAdmissionRanges`
- `R1Z.BuilderAdmissionRecords`
- `R1Z.BuilderAdmissionStd`
- `R1Z.BuilderBankCells`
- `R1Z.BuilderBankCollect`
- `R1Z.BuilderBankExtracted`
- `R1Z.BuilderBankMaterialization`
- `R1Z.BuilderBankMerge`
- `R1Z.BuilderBankRange`
- `R1Z.BuilderBankShape`
- `R1Z.BuilderBankStep`
- `R1Z.BuilderCanonical`
- `R1Z.BuilderColumns`
- `R1Z.BuilderColumnsExtracted`
- `R1Z.BuilderExtractedRecords`
- `R1Z.BuilderFieldNormalization`
- `R1Z.BuilderNullifierExtracted`
- `R1Z.BuilderNullifierReference`
- `R1Z.BuilderPartsContent`
- `R1Z.BuilderPrimitiveArguments`
- `R1Z.BuilderPrimitiveWriters`
- `R1Z.BuilderProtocolBounds`
- `R1Z.BuilderProtocolInstance`
- `R1Z.BuilderPublicCanonical`
- `R1Z.BuilderRecordCanonical`
- `R1Z.BuilderRecordsAdmission`
- `R1Z.BuilderRecordsArray`
- `R1Z.BuilderRecordsBankStd`
- `R1Z.BuilderRecordsExtracted`
- `R1Z.BuilderRecordsFields`
- `R1Z.BuilderRecordsMatrix`
- `R1Z.BuilderRecordsP6`
- `R1Z.BuilderRecordsPath`
- `R1Z.BuilderRecordsPublic`
- `R1Z.BuilderRecordsRecipient`
- `R1Z.BuilderRecordsReference`
- `R1Z.BuilderRefinement`
- `R1Z.BuilderRuntimeJoin`
- `R1Z.BuilderSliceCollect`
- `R1Z.BuilderSource`
- `R1Z.BuilderStdArray`
- `R1Z.BuilderStdCollect`
- `R1Z.BuilderStdModels`
- `R1Z.BuilderStdShift`
- `R1Z.BuilderTransport`
- `R1Z.BuilderTransportExtracted`
- `R1Z.BuilderTreeCarry`
- `R1Z.BuilderTreeCarryExtracted`
- `R1Z.BuilderTreeStep`
- `R1Z.BuilderTreeStepExtracted`
- `R1Z.PDict_Advance244`
- `R1Z.PDict_Array32`
- `R1Z.PDict_ArrayReference244`
- `R1Z.PDict_Audit231`
- `R1Z.PDict_CarrierInstall`
- `R1Z.PDict_CarriersSource`
- `R1Z.PDict_CodecDictionary`
- `R1Z.PDict_CodecSource`
- `R1Z.PDict_Compare`
- `R1Z.PDict_ConstantsSource`
- `R1Z.PDict_CopyCell244`
- `R1Z.PDict_CopyCorrect244`
- `R1Z.PDict_CopySource244`
- `R1Z.PDict_CryptoTypesSource`
- `R1Z.PDict_CtConstructor`
- `R1Z.PDict_CtUpdate`
- `R1Z.PDict_DigestDelegates`
- `R1Z.PDict_DigestNew`
- `R1Z.PDict_ErrorCarrier`
- `R1Z.PDict_ErrorKind`
- `R1Z.PDict_Fence`
- `R1Z.PDict_FileCarrier`
- `R1Z.PDict_FileFlush`
- `R1Z.PDict_FileWorld244`
- `R1Z.PDict_FinalDictionary`
- `R1Z.PDict_FormatterQuotient244`
- `R1Z.PDict_IOCarriers`
- `R1Z.PDict_Installed`
- `R1Z.PDict_MaskError`
- `R1Z.PDict_MoreCarriers`
- `R1Z.PDict_Numeric`
- `R1Z.PDict_OffpathBorrow`
- `R1Z.PDict_Options`
- `R1Z.PDict_Ordering`
- `R1Z.PDict_OwnedSource244`
- `R1Z.PDict_PathRefSource`
- `R1Z.PDict_PathTypesSource`
- `R1Z.PDict_Primitives`
- `R1Z.PDict_Publication`
- `R1Z.PDict_PureDictionary`
- `R1Z.PDict_PureSource`
- `R1Z.PDict_RejectionStd`
- `R1Z.PDict_RejectionStdSource`
- `R1Z.PDict_RemainingCaller231`
- `R1Z.PDict_RemainingCommute231_01`
- `R1Z.PDict_RemainingCommute231_02`
- `R1Z.PDict_RemainingCommute231_03`
- `R1Z.PDict_RemainingCommute231_04`
- `R1Z.PDict_RemainingCommute231_05`
- `R1Z.PDict_RemainingCommute231_06`
- `R1Z.PDict_RemainingCommute231_07`
- `R1Z.PDict_RemainingCommute231_08`
- `R1Z.PDict_RemainingCommute231_09`
- `R1Z.PDict_RemainingCommute231_10`
- `R1Z.PDict_RemainingCommute231_11`
- `R1Z.PDict_RemainingCommute231_12`
- `R1Z.PDict_RemainingCommute231_13`
- `R1Z.PDict_RemainingCommute231_14`
- `R1Z.PDict_RemainingCommute231_15`
- `R1Z.PDict_RemainingCommute231_16`
- `R1Z.PDict_RemainingCommute231_17`
- `R1Z.PDict_RemainingCommute231_18`
- `R1Z.PDict_RemainingCommute231_19`
- `R1Z.PDict_RemainingCommute231_20`
- `R1Z.PDict_RemainingCommute231_21`
- `R1Z.PDict_RemainingCommute231_22`
- `R1Z.PDict_RemainingCommute231_23`
- `R1Z.PDict_RemainingCommute231_24`
- `R1Z.PDict_RemainingCommute231_25`
- `R1Z.PDict_RemainingCommute231_26`
- `R1Z.PDict_RemainingCommute231_27`
- `R1Z.PDict_RemainingCommute231_28`
- `R1Z.PDict_RemainingCommute231_29`
- `R1Z.PDict_RemainingCommute231_30`
- `R1Z.PDict_RemainingCommute231_31`
- `R1Z.PDict_RemainingCommute231_32`
- `R1Z.PDict_RemainingCommute231_33`
- `R1Z.PDict_RemainingCommute231_34`
- `R1Z.PDict_RemainingCommute231_35`
- `R1Z.PDict_RemainingCommute231_36`
- `R1Z.PDict_RemainingCommute231_37`
- `R1Z.PDict_RemainingCommute231_38`
- `R1Z.PDict_RemainingCommute231_39`
- `R1Z.PDict_RemainingDictionary231`
- `R1Z.PDict_RemainingExt231`
- `R1Z.PDict_RemainingLeafSource`
- `R1Z.PDict_RemainingValues231`
- `R1Z.PDict_ReserveErrorSource`
- `R1Z.PDict_ResumeDictionary`
- `R1Z.PDict_RetryCap`
- `R1Z.PDict_RowBounds244`
- `R1Z.PDict_RowChunk244_0`
- `R1Z.PDict_RowChunk244_1`
- `R1Z.PDict_RowChunk244_2`
- `R1Z.PDict_RowChunk244_3`
- `R1Z.PDict_RowChunk244_4`
- `R1Z.PDict_RowChunk244_5`
- `R1Z.PDict_RowChunk244_6`
- `R1Z.PDict_RowChunk244_7`
- `R1Z.PDict_RowTable244`
- `R1Z.PDict_SHAConstructorSource`
- `R1Z.PDict_SaltClear`
- `R1Z.PDict_StatementTypesSource`
- `R1Z.PDict_TapeCells244`
- `R1Z.PDict_TapeCorrect244`
- `R1Z.PDict_TapeSource244`
- `R1Z.PDict_TapeView244`
- `R1Z.PDict_Typenum`
- `R1Z.PDict_UIntOps`
- `R1Z.PDict_UIntSource`
- `R1Z.PDict_VolatileCell`
- `R1Z.PDict_WireError`
- `R1Z.PDict_World244`
- `R1Z.PV_CB3_Afterstate`
- `R1Z.PV_CB3_Op225Source`
- `R1Z.PV_CB3_Op229Source`
- `R1Z.PV_CB3_Op246Source`
- `R1Z.PV_RunJoin_CallerWorld`
- `R1Z.PV_RunJoin_World`
- `R1Z.PhaseLeafEncodingBin`
- `R1Z.PhaseProtocolCoverageBin`
- `R1Z.PhaseProtocolInstanceBin`
- `R1Z.PhaseSamplerParserBin`
- `R1Z.PhaseWireLog2Bin`
- `R1Z.PhaseWireOrdered16`
- `R1Z.PrivacyBoundR1PBin`
- `R1Z.PrivacyPremisesBin`
- `R1Z.PrivacyR1AcctBasis`
- `R1Z.PrivacyR1AcctModel`
- `R1Z.PrivacyR1Final`
- `R1Z.PrivacyR1FinalProtocol`
- `R1Z.PrivacyR1FinalProtocolBuilder`
- `R1Z.PrivacyR1FinalProtocolCaller`
- `R1Z.PrivacyR1FinalProtocolHistory`
- `R1Z.PrivacyR1FinalProtocolHistoryReal`
- `R1Z.PrivacyR1FinalProtocolQuotient`
- `R1Z.PrivacyR1FinalRelease`
- `R1Z.PrivacyR1FinalReleaseSource`
- `R1Z.PrivacyR1FinalReleaseSource2`
- `R1Z.PrivacyR1FinalReleaseSource3`
- `R1Z.PrivacyR1Headline`
- `R1Z.PrivacyR1HeadlineAcct`
- `R1Z.PrivacyR1HeadlineDeployed`
- `R1Z.PrivacyR1HeadlineDeployedReal`
- `R1Z.PrivacyR1HeadlineOwned`
- `R1Z.PrivacyR1HeadlineOwnedClosed`
- `R1Z.PrivacyR1HeadlineV2`
- `R1Z.PrivacyR1HeadlineWire2`
- `R1Z.PrivacySimulatorBin`
- `R1Z.ProverCommitAdmittedEndpoint`
- `R1Z.ProverCommitArray49`
- `R1Z.ProverCommitArrayIndex25`
- `R1Z.ProverCommitBasisCounter47`
- `R1Z.ProverCommitCallerInstance`
- `R1Z.ProverCommitCircle25`
- `R1Z.ProverCommitCircleProgram28`
- `R1Z.ProverCommitCircleSampler22`
- `R1Z.ProverCommitCoinCall27`
- `R1Z.ProverCommitCoinSequence27`
- `R1Z.ProverCommitCoinTape27`
- `R1Z.ProverCommitCompact43`
- `R1Z.ProverCommitControl28`
- `R1Z.ProverCommitControlProgram28`
- `R1Z.ProverCommitControlSource28`
- `R1Z.ProverCommitCursor`
- `R1Z.ProverCommitDeployedFuel22`
- `R1Z.ProverCommitDigest26`
- `R1Z.ProverCommitDomain34`
- `R1Z.ProverCommitEffectCallers27`
- `R1Z.ProverCommitEntropy34`
- `R1Z.ProverCommitEnvironment35`
- `R1Z.ProverCommitExtractedCoin27`
- `R1Z.ProverCommitExtractedStep`
- `R1Z.ProverCommitFields20`
- `R1Z.ProverCommitFields29`
- `R1Z.ProverCommitFieldsSource29`
- `R1Z.ProverCommitFixedEndpoint`
- `R1Z.ProverCommitFourSteps`
- `R1Z.ProverCommitFuelJoin22`
- `R1Z.ProverCommitFuelMass22`
- `R1Z.ProverCommitGamma48`
- `R1Z.ProverCommitInit28`
- `R1Z.ProverCommitInterpolationInverse48`
- `R1Z.ProverCommitInverse48`
- `R1Z.ProverCommitJointHistory19`
- `R1Z.ProverCommitLedger36`
- `R1Z.ProverCommitLedgerCoupling39`
- `R1Z.ProverCommitLimbBytes47`
- `R1Z.ProverCommitLogged28`
- `R1Z.ProverCommitM31Ops48`
- `R1Z.ProverCommitMerge33`
- `R1Z.ProverCommitMix48`
- `R1Z.ProverCommitModelCore16`
- `R1Z.ProverCommitMulU48`
- `R1Z.ProverCommitNative30`
- `R1Z.ProverCommitNativeC49`
- `R1Z.ProverCommitNativeCInverse49`
- `R1Z.ProverCommitNativeNeg49`
- `R1Z.ProverCommitNativeOps47`
- `R1Z.ProverCommitNativeQ48`
- `R1Z.ProverCommitNativeQInverse49`
- `R1Z.ProverCommitNativeQSquare49`
- `R1Z.ProverCommitNativeSquare49`
- `R1Z.ProverCommitObserverQueries19`
- `R1Z.ProverCommitOracleEffect26`
- `R1Z.ProverCommitOwnedArrayLaw`
- `R1Z.ProverCommitOwnedArrays`
- `R1Z.ProverCommitOwnedBackend`
- `R1Z.ProverCommitOwnedByteValue`
- `R1Z.ProverCommitOwnedBytes`
- `R1Z.ProverCommitOwnedCache`
- `R1Z.ProverCommitOwnedCallerLaw`
- `R1Z.ProverCommitOwnedCursorProgress`
- `R1Z.ProverCommitOwnedDecoder`
- `R1Z.ProverCommitOwnedEndpoint`
- `R1Z.ProverCommitOwnedModel`
- `R1Z.ProverCommitOwnedProgress`
- `R1Z.ProverCommitOwnedReadBound`
- `R1Z.ProverCommitOwnedSequence`
- `R1Z.ProverCommitOwnedTotal`
- `R1Z.ProverCommitOwnedWord`
- `R1Z.ProverCommitOwnerBytes42`
- `R1Z.ProverCommitOwnerZero42`
- `R1Z.ProverCommitPack25`
- `R1Z.ProverCommitPackWindows25`
- `R1Z.ProverCommitPairCounter47`
- `R1Z.ProverCommitPolicies25`
- `R1Z.ProverCommitPolicy23`
- `R1Z.ProverCommitPowers48`
- `R1Z.ProverCommitPrimitive47`
- `R1Z.ProverCommitPrivateMemo40`
- `R1Z.ProverCommitProduct25`
- `R1Z.ProverCommitProductOracle25`
- `R1Z.ProverCommitPublicBinding40`
- `R1Z.ProverCommitPublicFields34`
- `R1Z.ProverCommitPublicFrontier34`
- `R1Z.ProverCommitPublicImage33`
- `R1Z.ProverCommitPublicNonce40`
- `R1Z.ProverCommitPublicRawBridge34`
- `R1Z.ProverCommitPublicSuccess34`
- `R1Z.ProverCommitPublicWhole34`
- `R1Z.ProverCommitPublication33`
- `R1Z.ProverCommitPublish43`
- `R1Z.ProverCommitQOps48`
- `R1Z.ProverCommitQuery26`
- `R1Z.ProverCommitQueryTotal26`
- `R1Z.ProverCommitReencode16`
- `R1Z.ProverCommitReferenceReads`
- `R1Z.ProverCommitReferenceSource`
- `R1Z.ProverCommitRelease47`
- `R1Z.ProverCommitReservationFrames37`
- `R1Z.ProverCommitReservationGuess38`
- `R1Z.ProverCommitReservationMemo37`
- `R1Z.ProverCommitReservationMemo39`
- `R1Z.ProverCommitReservationNonzero37`
- `R1Z.ProverCommitReservationRom37`
- `R1Z.ProverCommitRetry34`
- `R1Z.ProverCommitRetrySource34`
- `R1Z.ProverCommitRows29`
- `R1Z.ProverCommitSaltBytes`
- `R1Z.ProverCommitSaltSource`
- `R1Z.ProverCommitSamplerComposition`
- `R1Z.ProverCommitScalar48`
- `R1Z.ProverCommitSeedEvent19`
- `R1Z.ProverCommitSeedJoin19`
- `R1Z.ProverCommitSemantic20`
- `R1Z.ProverCommitSemanticProgram28`
- `R1Z.ProverCommitSemanticRows28`
- `R1Z.ProverCommitSemanticSampler22`
- `R1Z.ProverCommitSemanticSource28`
- `R1Z.ProverCommitSemanticTransport26`
- `R1Z.ProverCommitSequentialArrays`
- `R1Z.ProverCommitSequentialFibres`
- `R1Z.ProverCommitSimulatorCoin18`
- `R1Z.ProverCommitSimulatorInsert19`
- `R1Z.ProverCommitSimulatorOracle18`
- `R1Z.ProverCommitSimulatorSeedGuess18`
- `R1Z.ProverCommitSourceCallerLaw`
- `R1Z.ProverCommitSourceCounts`
- `R1Z.ProverCommitSourceDecoder`
- `R1Z.ProverCommitSourceExhaustion`
- `R1Z.ProverCommitSourceFailure`
- `R1Z.ProverCommitSourceSuccess`
- `R1Z.ProverCommitStateLift28`
- `R1Z.ProverCommitStep29`
- `R1Z.ProverCommitStepLoop`
- `R1Z.ProverCommitStepSource29`
- `R1Z.ProverCommitStreamBytes`
- `R1Z.ProverCommitStreamPack25`
- `R1Z.ProverCommitStreamSource`
- `R1Z.ProverCommitSubDecode47`
- `R1Z.ProverCommitSubRaw47`
- `R1Z.ProverCommitSubfieldOps47`
- `R1Z.ProverCommitSubtraction47`
- `R1Z.ProverCommitTable20`
- `R1Z.ProverCommitTablePrefix21`
- `R1Z.ProverCommitTail21`
- `R1Z.ProverCommitTreeMap22`
- `R1Z.ProverCommitTreeOps23`
- `R1Z.ProverCommitTrustedStd24`
- `R1Z.ProverCommitValueRange47`
- `R1Z.ProverCommitWalk28`
- `R1Z.ProverCommitWalk29`
- `R1Z.ProverCommitWideArray48`
- `R1Z.ProverCommitWideBytes48`
- `R1Z.ProverCommitWideOps48`
- `R1Z.ProverCommitWideQM31Scalar49`
- `R1Z.ProverCommitWordBytes47`
- `R1Z.ProverCommitWordCarrier`
- `R1Z.ProverCommitWrapping47`
- `R1Z.ProverRwBodyCandidateData`
- `R1Z.ProverRwBodyCandidateStore`
- `R1Z.ProverRwBodyDataCriterion`
- `R1Z.ProverRwBodyErrorData`
- `R1Z.ProverRwBodyNativeWideInstall`
- `R1Z.ProverRwBodyReservationTransport`
- `R1Z.ProverRwBodyStore`
- `R1Z.ProverRwBodyStoreSource`
- `R1Z.ProverRwCallerBinding`
- `R1Z.ProverRwDictionaryBaseField`
- `R1Z.ProverRwDictionaryBytes`
- `R1Z.ProverRwDictionaryBytesSource`
- `R1Z.ProverRwDictionaryConstants`
- `R1Z.ProverRwDictionaryDerived`
- `R1Z.ProverRwDictionaryDerivedSource`
- `R1Z.ProverRwDictionaryDigest`
- `R1Z.ProverRwDictionaryDomain`
- `R1Z.ProverRwDictionaryEmbedding`
- `R1Z.ProverRwDictionaryLayout`
- `R1Z.ProverRwDictionaryLayoutSource`
- `R1Z.ProverRwDictionaryMerkle`
- `R1Z.ProverRwDictionaryOption`
- `R1Z.ProverRwDictionaryOptionSource`
- `R1Z.ProverRwDictionaryScalar`
- `R1Z.ProverRwDictionaryTower`
- `R1Z.ProverRwDictionaryWideQM`
- `R1Z.ProverRwEntropyIteration`
- `R1Z.ProverRwEntropyObstruction`
- `R1Z.ProverRwFullExternalFuns`
- `R1Z.ProverRwFullExternalTypes`
- `R1Z.ProverRwFullFuns`
- `R1Z.ProverRwFullSampler`
- `R1Z.ProverRwFullTypes`
- `R1Z.ProverRwOuterAfterChecks`
- `R1Z.ProverRwOuterBytes`
- `R1Z.ProverRwOuterCaller`
- `R1Z.ProverRwOuterContext`
- `R1Z.ProverRwOuterContextModel`
- `R1Z.ProverRwOuterEncode`
- `R1Z.ProverRwOuterFrames`
- `R1Z.ProverRwOuterGuardBridge`
- `R1Z.ProverRwOuterGuardLeaves`
- `R1Z.ProverRwOuterInstalled`
- `R1Z.ProverRwOuterMapErr`
- `R1Z.ProverRwOuterPrefix`
- `R1Z.ProverRwOuterPrepare`
- `R1Z.ProverRwOuterTag`
- `R1Z.ProverRwOuterWrite`
- `R1Z.ProverRwP6ArrayMap`
- `R1Z.ProverRwP6ArrayMutRead`
- `R1Z.ProverRwP6ArrayRead`
- `R1Z.ProverRwP6BaseTotal`
- `R1Z.ProverRwP6BindTotal`
- `R1Z.ProverRwP6BodyCandidate`
- `R1Z.ProverRwP6BodyData`
- `R1Z.ProverRwP6BodyGamma`
- `R1Z.ProverRwP6BodyGammaPort`
- `R1Z.ProverRwP6BodyStore`
- `R1Z.ProverRwP6BoundaryInstall`
- `R1Z.ProverRwP6BoundaryReduce`
- `R1Z.ProverRwP6BoundarySource`
- `R1Z.ProverRwP6BoundaryStep`
- `R1Z.ProverRwP6BoundaryTotal`
- `R1Z.ProverRwP6ComplexTotal`
- `R1Z.ProverRwP6FlatInstall`
- `R1Z.ProverRwP6FlatSource`
- `R1Z.ProverRwP6FlatTotal`
- `R1Z.ProverRwP6PowersCongruence`
- `R1Z.ProverRwP6PowersControl`
- `R1Z.ProverRwP6PowersCoordinates`
- `R1Z.ProverRwP6PowersFinite`
- `R1Z.ProverRwP6PowersGammaSource`
- `R1Z.ProverRwP6PowersGammaValues`
- `R1Z.ProverRwP6PowersInstall`
- `R1Z.ProverRwP6PowersNativeBridge`
- `R1Z.ProverRwP6PowersNativeCaller`
- `R1Z.ProverRwP6PowersNativeFactor`
- `R1Z.ProverRwP6PowersNativeStep`
- `R1Z.ProverRwP6PowersRunTotal`
- `R1Z.ProverRwP6PowersSelectedTotal`
- `R1Z.ProverRwP6PowersSource`
- `R1Z.ProverRwP6PowersTotal`
- `R1Z.ProverRwP6QuarticTotal`
- `R1Z.ProverRwP6ResultMap`
- `R1Z.ProverRwP6TransitionInstall`
- `R1Z.ProverRwP6TransitionSource`
- `R1Z.ProverRwP6TransitionTransport`
- `R1Z.ProverRwP6WideDecode`
- `R1Z.ProverRwP6WideTotal`
- `R1Z.ProverRwP7FibreSource`
- `R1Z.ProverRwP7ReverseSource`
- `R1Z.ProverRwP7TraceCloneInstall`
- `R1Z.ProverRwP7TraceCloneSource`
- `R1Z.ProverRwP7TraceCloneTotal`
- `R1Z.ProverRwQueryAttempt`
- `R1Z.ProverRwQueryBlock`
- `R1Z.ProverRwQueryCallerSplit`
- `R1Z.ProverRwQueryComplete`
- `R1Z.ProverRwQueryContains`
- `R1Z.ProverRwQueryDecode`
- `R1Z.ProverRwQueryExecution`
- `R1Z.ProverRwQueryFinishTransport`
- `R1Z.ProverRwQueryInstalled`
- `R1Z.ProverRwQueryListStep`
- `R1Z.ProverRwQueryMaterial`
- `R1Z.ProverRwQueryMaterialTransport`
- `R1Z.ProverRwQueryMembership`
- `R1Z.ProverRwQueryModelChain`
- `R1Z.ProverRwQueryNativeAttempt`
- `R1Z.ProverRwQueryOpening`
- `R1Z.ProverRwQueryPolicy`
- `R1Z.ProverRwQueryPublish`
- `R1Z.ProverRwQueryResult`
- `R1Z.ProverRwQueryRetry`
- `R1Z.ProverRwQueryScan`
- `R1Z.ProverRwQuerySemantics`
- `R1Z.ProverRwQuerySourceWindow`
- `R1Z.ProverRwQueryStop`
- `R1Z.ProverRwQueryTrace`
- `R1Z.ProverRwQueryTransition`
- `R1Z.ProverRwQueryWindow`
- `R1Z.ProverRwQueryWindowStop`
- `R1Z.ProverRwQueryWord`
- `R1Z.ProverRwQueryWordTotal`
- `R1Z.ProverRwRetryModel`
- `R1Z.ProverRwRngCallerComposition`
- `R1Z.ProverRwRngCallerControl`
- `R1Z.ProverRwRngCallerEmission`
- `R1Z.ProverRwRngCallerEntropy`
- `R1Z.ProverRwRngCallerEvents`
- `R1Z.ProverRwRngCallerReplay`
- `R1Z.ProverRwRngCallerStep`
- `R1Z.ProverRwRngControl`
- `R1Z.ProverRwRngEmission`
- `R1Z.ProverRwRngNativeBodyEmission`
- `R1Z.ProverRwRngNativeBodyLeaves`
- `R1Z.ProverRwRngNativeBodyTypes`
- `R1Z.ProverRwRngNonzero`
- `R1Z.ProverRwRngOwnerBridge`
- `R1Z.ProverRwRngOwnerCertificate`
- `R1Z.ProverRwRngOwnerDraw`
- `R1Z.ProverRwRngOwnerEmission`
- `R1Z.ProverRwRngOwnerEvents`
- `R1Z.ProverRwRngOwnerInduction`
- `R1Z.ProverRwRngOwnerInventory`
- `R1Z.ProverRwRngOwnerState`
- `R1Z.ProverRwRngOwnerStep`
- `R1Z.ProverRwRngTape`
- `R1Z.ProverRwRngTransportValidity`
- `R1Z.ProverRwSamplerArithmetic`
- `R1Z.ProverRwSamplerModel`
- `R1Z.ProverRwSamplerTransport`
- `R1Z.ProverRwSemanticSampler`
- `R1Z.ProverRwSuccessArithmeticTotal`
- `R1Z.ProverRwSuccessArrayFromFn`
- `R1Z.ProverRwSuccessBodyInterpretation`
- `R1Z.ProverRwSuccessBorrow`
- `R1Z.ProverRwSuccessByteEquality`
- `R1Z.ProverRwSuccessCoefficientsSource`
- `R1Z.ProverRwSuccessComplexInverseExact`
- `R1Z.ProverRwSuccessComplexOperations`
- `R1Z.ProverRwSuccessConstants`
- `R1Z.ProverRwSuccessCtReduce`
- `R1Z.ProverRwSuccessCtSubtract`
- `R1Z.ProverRwSuccessEquality`
- `R1Z.ProverRwSuccessErrorInstall`
- `R1Z.ProverRwSuccessErrorSource`
- `R1Z.ProverRwSuccessField`
- `R1Z.ProverRwSuccessGeneric`
- `R1Z.ProverRwSuccessHashes`
- `R1Z.ProverRwSuccessHeapInstall`
- `R1Z.ProverRwSuccessHeapSource`
- `R1Z.ProverRwSuccessInverseInstall`
- `R1Z.ProverRwSuccessInverseSource`
- `R1Z.ProverRwSuccessInverseTotal`
- `R1Z.ProverRwSuccessNativeInverseTransport`
- `R1Z.ProverRwSuccessNativeNegInstall`
- `R1Z.ProverRwSuccessNativeNormalize`
- `R1Z.ProverRwSuccessNativeNormalizeWord`
- `R1Z.ProverRwSuccessNativePorts`
- `R1Z.ProverRwSuccessNativeWideInstall`
- `R1Z.ProverRwSuccessNativeWideTransport`
- `R1Z.ProverRwSuccessOptions`
- `R1Z.ProverRwSuccessParser`
- `R1Z.ProverRwSuccessParserSource`
- `R1Z.ProverRwSuccessPhiSource`
- `R1Z.ProverRwSuccessPointsSource`
- `R1Z.ProverRwSuccessPowerExact`
- `R1Z.ProverRwSuccessPowerTotal`
- `R1Z.ProverRwSuccessQuarticInverseExact`
- `R1Z.ProverRwSuccessQuarticOperations`
- `R1Z.ProverRwSuccessScalarInverseExact`
- `R1Z.ProverRwSuccessVectors`
- `R1Z.ProverRwSuccessWideSource`
- `R1Z.ProverRwSuccessWireInstall`
- `R1Z.ProverRwSuccessWireSource`
- `R1Z.QueryScanFirstStopHistory`
- `R1Z.QueryScanFreshInputs`
- `R1Z.QueryScanFreshNumerics`
- `R1Z.QueryScanFreshUnion`
- `R1Z.QueryScanIdealHistory`
- `R1Z.QueryScanIndependentHistory`
- `R1Z.QueryScanRealEntropy`
- `R1Z.QueryScanRealFreshMass`
- `R1Z.QueryScanRealLazyBound`
- `R1Z.QueryScanRealLazyJoin`
- `R1Z.QueryScanSharedHistoryMass`
- `R1Z.QueryScanSharedHistoryObstruction`
- `R1Z.SerJoinOrderObstruction`
- `TerminalArrayFromFnModelV4Clean`
- `TerminalStandardOperationModelsV1`
