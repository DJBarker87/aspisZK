# PIN2 W3c: the Rust-bytes hinge on the PIN2 emission, the clash fix, stand-in retirement, and the M10 stages

Worker W3c, branch `fix/pin2-lean-20261110`, worktree `/Users/dominic/ZK/.worktrees/pin2-lean`. Nothing was pushed and nothing ran on the build host. Every compile was a single local `lean -M7000 -DElab.async=false` process under a 180 s alarm, through `evidence/pin2-w3c-20261111/PIN2W3c_compile.sh`. That wrapper is W3a's, with a refusal to write through a symlink. The search path was `overlay-PIN2 : objs : base`, and objects were written into `overlay-PIN2` through a temporary file and a rename. The compile table is `PIN2-W3c-COMPILE.tsv`, which also holds the source sha, the revision and the overlay object hash before and after. Logs are in `evidence/pin2-w3c-20261111/logs/`.

Totals: 2,552 compiles, 2,518 of them exit 0, covering 1,334 distinct modules. The longest wall time was 25.4 s and the peak RSS was 5.67 GB (one process at a time). Every credited `#print axioms` line shows only `propext`, `Classical.choice` and `Quot.sound`. The 34 non-zero exits were the probes and first attempts described below, each followed by a fix or a classification; none is credited. No sorry, axiom, `native_decide` or heartbeat change was added. The only `maxHeartbeats` lines in touched files are the Aeneas emission default (1000000) in Stream C's emissions and `200000` (the default) in the probe-crate emission. Nothing was deleted: superseded files were moved to `evidence/pin2-w3c-20261111/quarantine/`.

## Step 1. Discriminant-instance clash (coordinator item, W4's finding)

The PIN2 emission `PIN2_NEWGATE_r0` and the release gate module `AspisR1FinishRelationCurrent.Types` both carried a top-level `instDiscriminantErrorIsize`. That name is the auto-generated name of the anonymous instance that Aeneas's `@[discriminant isize]` attribute elaborates. The gate side is frozen and read-only, so the fix had to go into the overlay copy of r0, and of r1_semantic for its own `r1_wire.Error`.

Each attribute was replaced by exactly what it generates: `<Ty>.read_discriminant` with values 0..n-1 in constructor order, plus an explicitly named instance inside `AspisR1PublicPreparationPIN2`. There are four such instances. Nothing in either emission uses them. The `public_bytes` text and every function are byte-identical (sha256 prefix 19015aca48f26f74 of the tail, before and after).

`evidence/pin2-w3c-20261111/CLASH-FIX.md` has the unified diffs and both sets of hashes:

- r0: `.lean` 92162163… → 949d0070…, `.olean` f9ade0b9… → 0c29efc8…
- r1_semantic: `.lean` b5ff0038… → b0a096b0…, `.olean` 7b590c58… → c89ff3f1…

Stream C should mirror this in its next emission. After the edit, all 1,185 overlay objects whose import closure contains r0 were force-rebuilt in import order (C1323–C2507), with 0 failures. The module that showed the clash, `RPz7_CurrentCompactInstalledPreparationV1`, now compiles (C2543).

## Item 1 (step 2). The hinge: PublicSerializerWhole431 and the two bridge-431 modules

**`PIN2_PublicSerializerWhole` (new, C1325).** This is the PIN2 counterpart of `PublicSerializerWhole431`, as the coordinator asked. For the PIN2 generated `public_bytes`:

- `program_canonical`: a successful run of W3b's PIN2 step program proves every serialized field word canonical.
- `source_success`: in the release form, the bytes equal `(steps p).flatMap stepBytes` and the words are canonical. There is no capacity or allocator premise.

The release `PublicSerializerWhole431` is unchanged. It stays valid for the frozen extraction and is still imported, as before, through W3b's modules for its generic helpers (`bind_success`, `push_success`, the 4.31 encoders). It is not in the R0P/PIN2 cone, so the host needs the release object `objs/PublicSerializerWhole431.olean` (sha 9fb84b37…), not a rebuild.

**`PublicExtractedRawBridge431` (edited, C1326).** The bridge is now stated about the PIN2 emission:

- `RawBridge431.Public` and `Transition` are now the PIN2 re-extraction's carrier types.
- `project` copies `pool` and `deployment_domain` into `Common`, and for a withdrawal it copies `destination_token_account`, through the new `rawBytes32`.
- `project_words` and `project_bytes` are stated over W3b's PIN2 `steps`/`stepBytes`.
- `source_success_raw`, `ExtractedReturns` and `extracted_refines_core` name the PIN2 `public_bytes`.

The proofs are the release ones plus `PublicRawCore.bindingBytes`.

**`WithdrawalCarrierBridge431` (edited, C1327).** `SerializerPublic` is the PIN2 `PoolV1WithdrawalPublicV1` (the same nine fields), the transition is `RawBridge431.Transition`, and `validated_source_success` names the PIN2 `public_bytes`. The proofs are unchanged.

Statements whose text changed (before → after):

- `RawBridge431.project : Whole431.Public → PublicRawCore.Public` → `RawBridge431.Public (PIN2 carrier) → PublicRawCore.Public`, with the binding suffix copied.
- `RawBridge431.project_words`, `project_bytes`: `(sourceSteps p).flatMap …` → `(PIN2_PublicBytesRefinement.steps p).flatMap …`.
- `source_success_raw`, `ExtractedReturns`, `extracted_refines_core`: frozen `pool_v1…r0.Public.public_bytes p` → `AspisR1PublicPreparationPIN2.pool_v1…r0.Public.public_bytes p`. The conclusions are unchanged (`PublicRawCore.serialize (project p) = some bytes`).
- `WithdrawalCarrier431.validated_source_success` and `helper_success_raw_amount_guard/nonzero`: `t : Whole431.Transition` → `t : RawBridge431.Transition`, and the `hs` producer is the PIN2 one.

**Direct consumers that the new types forced to change.** The edits are type retargets: `Whole431.{Public,Transition,Transfer,Withdrawal}` → the PIN2 carrier types, and the frozen `public_bytes` → the PIN2 one. Proofs are unchanged; the diffs are in `evidence/pin2-w3c-20261111/edits/` and the sources are in `sources/`.

- `ExtractedPublicCheckedBridge432`: hand edit.
- `ExtractedAdapterStageBindingObligations`: hand edit. `SerializerWitness` now names the PIN2 producer.
- `HchecksPublicComposition`, `DecoderInstanceBoundary`, `ExtractedDecoderPublicBinding`, `ExtractedDecoderPublicBridge` and `ExtractedWithdrawalCallerPublic`: the driver made the same mechanical retarget on a type-mismatch failure, and I reviewed each diff.
- `ExtractedWithdrawalCallerCarrier` rebuilt with its source unchanged.

**`ExtractedPublicPreparationBinding` (hand edit, C1668).** This one was not a retarget, and the automatic retarget was rejected (kept in `rejected-autoedits/`). Stream C's `PIN2_FUNCTION_DIFF.json` lists `PoolV1PairForestTerminalStatementV1::semantic_public` as unchanged, so `fromStatement`, `preparationPublic` and `actual_selector_eq` stay on its frozen extraction. `public_transcript` calls the changed `public_bytes`, so:

- A new `toPIN2` copies the frozen preparation carrier field for field into the PIN2 carrier.
- `projection_eq`: `toOld (preparationPublic s) = toSerializer s` → `toPIN2 (preparationPublic s) = toSerializer s`.
- `helper_supplies_serializer_success` and `decoder_helper_parsePublic`:
  - `D` is now a PIN2 `aspis_core.digest.Digest32 H` and `out` a PIN2 `r1_wire.SemanticTranscript H`.
  - The premise `h` is now `AspisR1PublicPreparationPIN2.r1_semantic.public_transcript D (toPIN2 (preparationPublic s)) hash c1 = ok (.Ok out)`.
  - The conclusion names the PIN2 `public_bytes` and the PIN2 `SemanticTranscript.new`.
  - The proof is W3b's `PIN2_NHG_PublicCarrier.same_execution`.

Its consumer `RPv_PreparationPublicFieldsCanonical` was restated the same way (C2367): the same three binder types, and `h` now on the PIN2 transcript of `toPIN2 (preparationPublic s)`. Its conclusion `PublicSourceRaw.Canonical (projectRaw s)` is unchanged.

## Item 2 (step 3). M10 extractor stages

`ActualExtractorStagesM10` and `CostedExtractorStagesM10` compiled from W3b's branch source (C0093/C0084), together with the 89 unchanged modules of their chain, all exit 0. Their only change is the budget literal 110260 → 110542, and no proof needed anything beyond it. Their r0-cone objects were rebuilt again after the clash fix.

## Step 4. Stand-in retired; RPv_FIz_*OnRun

**The probe emission.** Stream C's probe-crate emission `PRVEq_PIN2_ProbeSemanticPublicProjection` imports `FIq_NativeTypes`, which does not exist under that name in the L187 closure. The closure's name for the same gate file is `RPu_FIq_NativeTypes`: blob 63498d98, the source with sha cdc1db1e… that Stream C names, recompiled as `RPu_FIq_NativeTypes`, gives a byte-identical object.

I therefore compiled `PIN2P_ProbeProjectionRPu` (C2508). It is Stream C's text with only that import line changed. Stream C should re-emit with `import RPu_FIq_NativeTypes`, after which the swap is that one import.

**The helpers.** `PIN2_ProbeSemanticPublicHelpers` (C2509) keeps only what the emission does not provide: the `byte`/`bytes32` helpers, the rfl field-projection simp lemmas over the emitted `dropDestination`, and the `pin2_drop` tactic.

**The rebuild.** `RPv_FIw_PublicModel` now uses `PIN2P.SemanticPublic`. It and its 30 overlay dependents were force-rebuilt, 31 of 31 ok. The other W3a builders changed only in comments. No overlay object imports the stand-in, and its object was moved to `quarantine/overlay-PIN2/PIN2_SemanticPublicStandIn.olean` (sha 5961deb3…).

**OnRun.** `RPv_FIz_CoefficientsOnRun` (C2541) and `RPv_FIz_WideCoefficientsOnRun` (C2542) each had one change:

- `p : FIw_ScalarSuffix.Public` (pre-PIN2 native) → `p : FIw_PublicModel.Public` (PIN2P).
- `success : semantic_packed p o s = ok out` → `semantic_packed p.dropDestination o s = ok out`.
- The proof applies `FIy_NativeCoefficients.value` to `p.dropDestination`.
- The conclusions (with `ofPublic p`) are textually unchanged.

The struct is probe-crate provenance, HM-D at best.

## Item 3. digest_domain

The composition is written as `sources-host-only/PIN2_NHG_DigestDomain.lean`. Its statement is the release `NHG_Lengths.digest_domain` over the PIN2 carrier, and its size premise is W3b's `PIN2_NHG_Final.seed_size`.

It is not compiled on the Mac. `NGX_SemanticRuntime` imports `NGX_SemanticNew → … → NGK_COMBINED_IMPORT → RPx_Deployed`, which is 4,529 unbuilt affected modules including the NDO_JF* fixtures, so it is a host replay target. An uncredited probe with a local copy of `seedViews`/`seed_domain` elaborated it with the standard axioms; no object was written.

## Item 4/5. The W3b-blocked set and further rebuilds

`WireBindingRecordCodec` was already W3b's object. On the coordinator's instruction, step 5 was narrowed to changed-source modules. `RPz7_F3J_Public`, `RPz8_F3V_Public`, `NKR_DigestAssociation`, `NKR_DigestOptionalValue`, `RPv_FJq_PublicModel` (W3a-edited, not yet compiled) and `RPv_FJn_ModelInputs` sit on top of the unchanged-source chain, about 4,700 modules, which the host cold replay builds. I stopped the driver after the module in progress. The last unchanged rebuilds on the Mac were C2543–C2553.

I needed no source edit for F3J or F3V. NKR_* and FJn are additionally held behind the `NDO_JF*` fixtures.

Release sources for 59 ambiguous module names were settled by recompiling every candidate blob against the release closure. A candidate was accepted if its object was byte-identical, or differed only in the recorded source path ("PATHONLY", checked on the string tables). The results are in `AMBIGUOUS-VERIFY.tsv` and `VERIFIED-SOURCES.json`.

## Handover

`evidence/pin2-w3c-20261111/HANDOVER-MODULES.tsv` lists every W3c source with its sha256, overlay `.olean` sha256, compile id, wall time and RSS. These are the 25 modules of `sources/`:

- the four emission or probe copies;
- the two new PIN2 modules;
- the two bridges;
- nine consumer edits;
- seven FIw/FIz builders;
- the two OnRun modules.

`overlay-PIN2.before.sha256` and `overlay-PIN2.after.sha256` give the full overlay before (731 objects) and after (2,028 objects, no links).

Objects added to overlay-PIN2 after the coordinator's "narrow step 5" message: `RPz7_CurrentCompactInstalledPreparationV1`, `RPz7_CurrentOriginalPreparedNativeV1`, `RPz7_CurrentOriginalPreparedCarrierTransportV1`, `RPz7_CurrentOriginalPreparedInstallationV1`, `RPz7_S1BorrowedClaimPreparedBoundaryV1`, `RPz7_S1BorrowedClaimFirstCallerV1`, `RPz7_S1CurrentOwnedPreparedJoinV1`, `RPz7_S1QueryTraceEmbeddingV1`, `RPz7_S1OriginalPreparedSourceEmbeddingV1`, `RPz7_S1OriginalSerializerInstallationV1` and `RPz7_S1OriginalSerializedRankTraceV1` (C2543–C2553). All are unchanged release sources.

Quarantine contents: `quarantine/overlay-PIN2/PIN2_SemanticPublicStandIn.olean`. Superseded W3c copies are in `rejected-autoedits/`, which holds the rejected retarget of `ExtractedPublicPreparationBinding`.

## Remaining blockers, by owner

- **Stream C:**
  - Re-emit `PIN2_NEWGATE_r0` and `PIN2_NEWGATE_r1_semantic` with the named, namespaced discriminant instances (CLASH-FIX.md), and the probe-crate module with `import RPu_FIq_NativeTypes`.
  - Probe-crate provenance of `PIN2P.SemanticPublic` remains HM-D.
  - `ExtractedPublicPreparationBinding` relies on the PIN2_FUNCTION_DIFF classification of `semantic_public` as unchanged, and on the fresh-equals-gate claim for that function.
  - Downstream modules that consume `helper_supplies_serializer_success` with the frozen `Digest32`/`SemanticTranscript` types will need the same restatement; none beyond `RPv_PreparationPublicFieldsCanonical` was reached on the Mac.
- **Build host (replay):**
  - The unchanged-source chain (about 4,700 modules) up to `RPz7_F3J_Public`, `RPz8_F3V_Public`, `RPv_FJq_PublicModel` and `RPv_FJn_ModelInputs`.
  - `PIN2_NHG_DigestDomain`.
  - The coherent cold replay of the full closure and the axioms audit of the two top theorems.
- **Devnet regeneration:** the `NDO_JF*` fixtures, which hold back NKR_DigestAssociation, NKR_DigestOptionalValue, FJn and their dependents.
- **SAG_DotDecode:** it failed only on the clash (C0714/C0879) and should now compile in the replay.

The obligations closed here are:

- the source refinement of the PIN2 `public_bytes` to `PublicRawCore`, with the binding suffix carried, now proved against the actual PIN2 emission (`extracted_refines_core`);
- the withdrawal carrier bridge on the PIN2 carrier;
- the preparation binding on the PIN2 transcript;
- the compiled M10 stages at budget 110542;
- the retired stand-in;
- the repaired OnRun modules.

The PIN2 parse round trip and the release closure's top theorems are not re-established.

target not yet established
