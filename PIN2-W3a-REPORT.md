# PIN2 W3a: first-layer completion, mechanical downstream edits, DestinationShape discharge, coherent rebuild

Worker W3a, branch `fix/pin2-lean-20261110` on top of W2's `4b8b663b31d`, worktree `/Users/dominic/ZK/.worktrees/pin2-lean`. The evidence directory is `docs/research/100bit-spend-path-20261013/evidence/pin2-w3a-20261111/`. It holds the edited sources, the compile wrapper `PIN2W3a_compile.sh`, one log per compile, `REBUILD-STATUS.tsv`, `HOST-REBUILD-ORDER.tsv`, `PROVENANCE-UNCHANGED.tsv`, `superseded.txt`/`superseded.tsv` and `copied_nondep.txt`. The compile table is `PIN2-W3a-COMPILE.tsv` at the worktree root. Every compile was a single local `lean -M7000 -DElab.async=false` process under a 180 s alarm, run only while no other Lean process was running on the machine. Nothing ran on the build host and nothing was pushed.

The search path was `overlay-PIN2 : objs : base`. That is W2's script order, with the overlay first so that it shadows. The order written in the brief (objs first) would not shadow anything. Each new object was written to `overlay-PIN2` through a temporary file and then renamed, and every TSV row records the first 16 hex digits of the overlay object's sha256 before and after.

## 1. DestinationShape: discharged by the constructor shape, not carried as a premise

W2 put `destination` in `PublicSourceRaw.Common`, and that is why it needed a `DestinationShape` premise. The raw model is a shadow of Rust `r0::Public`. In `r0::Public`, `Withdrawal` carries `destination_token_account` (which `withdrawal_public` copies as `Some`) and `Transfer` has no destination (`private_public` sets `None`). The raw model already fixes the recipient and amount shapes through its constructors in the same way. So I moved the destination into the withdrawal constructor:

- `PublicSourceRaw.Public.withdrawal (common) (amount) (destination : Bytes32)`; `Common` keeps `pool` and `deploymentDomain`.
- `serialize` appends `encodeDestination none` for a transfer and `encodeDestination (some d)` for a withdrawal.
- `mapCommon` takes the destination as an argument.
- `DestinationShape` is now proved for every value: `theorem destinationShape (p) : DestinationShape p`.

Before and after, in `R1PublicSourceRawMap`:

- `mapPublic_canonical`, `mapped_canonical` and `decode_of_serialize` were, under W2, `... (hn : NonzeroWithdrawal p) (hd : DestinationShape p)`. They are now `... (hn : NonzeroWithdrawal p)`, which is exactly the release statement. The conclusions are unchanged.
- `serialize_rawPublic` gained a hypothesis, `(hw : WireDestinationShape wire)`. This is a genuine statement change: a transfer wire that carries a destination has no raw preimage. Its only in-closure use, `serialize_of_toWire`, discharges the hypothesis itself through the new `toWire_wireShape`.
- `afterBytes_rawCommon` now states the raw prefix plus `encodeDestination c.destination`. The new `afterBytes_rawCommon_some` gives the bare form.

Results for the five consumers W2 listed:

- `PublicSourceBoundary.parseRaw_of_source_success` (and the whole of `R1PublicSourceBoundary`): unchanged source, compiles, no new premise.
- `PublicSourceRawSuccess.decode_of_serialize` and `toWire_of_serialize`: release statements unchanged and no new premise. The only edit is the arity of one constructor pattern.
- `ExtractedPublicCheckedBridge432` and `ExtractedAdapterStageBindingObligations.parsePublic_of_wire_decode`: no source edit and no `DestinationShape` premise needed. Neither can be compiled yet, because both import `PublicExtractedRawBridge431` / `WithdrawalCarrierBridge431` (see section 5).

I probed `PublicExtractedRawBridge431` against the new `PublicRawCore` without writing an object, so the probe is not credited. It fails at `project` ("fields missing: pool, deploymentDomain") and at `extracted_refines_core`.

That is where the Rust fact now has to be proved. `RawBridge431.project` must copy the pool, the domain and, for `Withdrawal`, `destination_token_account` from the extracted serializer public. `extracted_refines_core` must show that the PIN2-extracted `public_bytes` emits the suffix. So the remaining obligation is one existing named refinement theorem, re-proved against Stream C's re-extraction of `r0::Public::public_bytes` and its callees. It is not a premise.

`PublicRawCore` (the shared pure core) gained the same suffix, with the destination in its withdrawal constructor. `PublicRawAmountGuard` needed pattern-arity edits only. In `PublicRawCoreAgreement`, `after_canonical` now includes pool and domain, `toCore` and `fromCore` copy the new fields, and `serialize_eq` and `serialize_fromCore` keep their statements. `PublicRawAmountGuardAgreement` compiles with an unchanged source.

The W2 impact scan missed `PublicRawCore`, `PublicRawCoreAgreement` and `PublicRawAmountGuard*`, because they did not refer to the watched names. They had to change all the same.

## 2. Modules edited

Every edited file is under `evidence/pin2-w3a-20261111/sources/`.

| File | Declarations | Nature of edit |
| --- | --- | --- |
| R1PublicSourceRaw | `Common`, `Public`, `Canonical`, `mapCommon`, `mapPublic`, `rawCommon`, `rawPublic`, `afterBytes`, `serialize`, `NonzeroWithdrawal`, `PaymentAmountGuard`; new `zeroBytes32`, `WireDestinationShape`, `destination`, `destinationShape` | destination moved to the withdrawal constructor; `DestinationShape` proved |
| R1PublicSourceRawMap | `rawCommon_mapCommon`, `rawPublic_mapPublic`, `afterBytes_rawCommon`, `serialize_rawPublic`, `serialize_of_toWire`, `mapPublic_canonical`, `mapped_canonical`, `decode_of_serialize`, `nonzero_of_payment_guard`; new `mapCommon_destination`, `mapPublic_wireShape`, `mapPublic_destination`, `afterBytes_rawCommon_some`, `toWire_wireShape` | W2's premise removed (back to the release statements); `serialize_rawPublic` gains a wire-shape hypothesis |
| R1PublicSourceRawSuccess | `serialize_success_canonical` (proof only) | pattern arity |
| PublicRawCore | `Bytes32` (new), `Common`, `Public`, `words`, `bindingBytes` (new), `encode` | PIN2 suffix |
| PublicRawAmountGuard | `PaymentAmountGuard`, `NonzeroWithdrawal`, `nonzero_of_payment_guard` | pattern arity |
| PublicRawCoreAgreement | `toCoreCommon`, `toCore`, `fromCoreCommon`, `fromCore`, `after_canonical` (statement), `serialize_canonical` (proof) | carry the suffix |
| PIN2_SemanticPublicStandIn (new, temporary) | `PIN2Native.SemanticPublic`, `OldSP`, `dropDestination`, `embed`, projection simp lemmas, `byte`, `bytes32`, tactic `pin2_drop` | stand-in for the native crate (see below) |
| R1SpendDataMap | `mapPublic`, `mapPublic_id`, `mapPublic_comp` | copy the three binding fields |
| R1SpendRelationMap | `canonical_map_iff` (proof) | unfold `bindingLengths` |
| RPv_FIw_PublicModel | `Public` (abbrev), `ofPublic` | reads the stand-in; pool/domain/destination via `bytes32` |
| RPv_FIz_ScalarFamily, DigestPrefix, DigestSuffix (`next`, `value`), PublicDigest, ScalarList, DigestFamily, ModelFamilies, SemanticAlignment, Retained24 | `value` / `next` | apply the pre-PIN2 native model to `p.dropDestination`; `pin2_drop` after unfolding |
| RPv_FJq_PublicModel | `common`, `model` | follow the raw constructor change (written; blocked from compiling, section 5) |

About the stand-in. Stream C's `PRVEq_PIN2_SemanticPublicProjection` emits only the `AspisR1PublicPreparation` crate's `SemanticPublic`. The group (b) builders, `FIw_PublicModel` and the `FIz_*` family, read the native crate `FIq_Native` (`RPu_FIq_NativeTypes`), and that crate has no PIN2 emission yet. `PIN2_SemanticPublicStandIn` therefore mirrors that crate's struct plus `destination : Option (Array U8 32#usize)`. It uses Stream C's field order and the same `dropDestination` / `embed` API. Every use carries the comment "replace by Stream C's PIN2 emission". Swapping it out takes one import line and one namespace (`PIN2Native` → Stream C's namespace). It is handwritten, not extracted. Nothing in this branch uses the PublicPreparation struct, so `PRVEq_PIN2_SemanticPublicProjection` is not yet imported anywhere.

These modules needed no edit and rebuilt clean: `R1AppendBindingMap`, `R1PublicBaseMap`, `RPv_DigestFamilyFieldTransport`, `RPv_FIz_DigestFrontier`, `RPv_FIz_OccupancyFamily`, `R1PublicSourceBoundary`, `PublicRawAmountGuardAgreement` and `R1SelectedTranscriptParams`. W2 expected an edit in `R1SelectedTranscriptParams`, but its `initFits` proof is `omega` against `L = 131072` and still closes at 1599.

`NKR_DigestAssociation`, `NKR_DigestOptionalValue` and `RPv_FJn_ModelInputs` are not edited. They read fields by name through `FIw_PublicModel.Public`, so I expect them to need only a rebuild, but they cannot be compiled before W3b's work lands.

## 3. Rebuilt clean

Of the 9 pending first-layer modules:

- **Rebuilt:** `SpendRelation`, `LiteralTerminalCandidate`, `R1LiteralTerminalSpend`, `RawCutWordsFromRunPublicValid` and `R1SelectedTranscriptParams`.
- **Blocked:** `ExtractedDecoderPublicBinding`, `ExtractedPublicCheckedBridge432`, `ExtractedAdapterStageBindingObligations` (all Stream C) and `RawCutWordsFromRunPublicValidBin` (its imports reach W3b's and Stream C's roots).

In total 671 modules are now coherent objects in `overlay-PIN2`, built in import order on top of W2's 27. These are the 8 manual edits and rebuilds of section 1, the stand-in, and 662 driver rebuilds, 25 of them edited. The full list, with compile IDs, is `REBUILD-STATUS.tsv` (`ok`) and `HOST-REBUILD-ORDER.tsv` (`done-W3a`).

Coherence checks:

- Every overlay object is newer than every overlay object it imports.
- The overlay contains no links.
- 379 of the 463 unchanged-source rebuilds checked have exactly the release object's identifier set. The others differ only in the host source path fragment or in the PIN2 field names, which is evidence that the right source was used.

How the sources were found. The release sources are not mapped anywhere in the repository. I took a module's source as known in one of three cases:

1. It was the only repository blob at that path (994 modules).
2. It was one of several candidates and recompiled against the old closure to a byte-identical object (verified).
3. It recompiled to an object that differed only in the recorded source path (PATHONLY).

`R1LiteralTranscript` was the one case where the unique same-named blob was wrong (it lacks the `R1UnifiedSampler` import). The byte-identical release source is a renamed copy, `LiteralTranscript.lean`, at blob `c545a721`.

## 4. Compile table (summary; every row is in PIN2-W3a-COMPILE.tsv)

There were 761 compiles: 736 exited 0 and 25 failed, each failure then fixed or classified. The longest wall time was 31 s, the peak RSS was 4.23 GiB, and the total compile wall time was 32 min. Every credited object prints only `propext`, `Classical.choice` and `Quot.sound`. The edited sources contain no sorry, axiom, `native_decide` or heartbeat change.

The wrapper's first axiom filter flagged `NJE_Pow5Packet` because a declaration name contains "native". The object was clean; the filter was fixed and the module recompiled. Representative rows (target, exit, wall s, peak RSS bytes):

- R1PublicSourceRaw: 0, 2.21, 2874392576 (C0001)
- R1PublicSourceRawMap: 0, 2.67, 2873671680 (C0003)
- R1PublicSourceRawSuccess: 0, 2.23, 2869018624 (C0004)
- R1PublicSourceBoundary: 0, 2.09, 2854715392 (C0005)
- PublicRawCore: 0, 0.46, 654032896 (C0006)
- PublicRawCoreAgreement: 0, 2.45, 2974171136 (C0008)
- PIN2_SemanticPublicStandIn: 0, 12.00, 2258059264 (C0487)
- RPv_FIw_PublicModel: 0, 6.39, 3230924800 (C0488)
- R1SpendDataMap: 0, 1.74, 2872492032 (C0336)
- R1SpendRelationMap: 0, 2.55, 2885402624 (C0531)
- SpendRelation: 0, 1.93, 2889695232 (C0312)
- R1SelectedTranscriptParams: 0, 1.83, 3052290048 (C0295)
- R1LiteralTranscript: 0, 2.05, 3074916352 (C0561)

## 5. Incident: overlay R0P links (00:37:56 to about 00:40)

When a module imported an R0P module that was not yet in the overlay, Lean stopped looking once it found the `overlay-PIN2/R0P/` directory. To work around that, I symlinked the 37 `objs/R0P` objects that were missing into `overlay-PIN2/R0P`. The coordinator removed the links and made `objs/` and `base/` read-only.

My wrapper writes through a temporary file and renames it, so no release object could be overwritten through a link, and the coordinator's mtime check confirms none was. The links were still a coherence hazard, and nothing compiled while they existed is credited. The 40 compiles concerned are listed in `superseded.txt`: `PIN2W3a_C0041` to `C0080`, from `R0P/LaneMap` through `RPv_FIz_ScalarFamily`. All 40 were rerun with no links present.

The chain the coordinator named was then rebuilt as regular objects in import order. Each was compiled after the fix:

- SemDecision C0163, SemD2 C0268, SemD2Glue C0321, SemD3 C0256, SemD3Glue C0311, SemRounds C0241, SemClosed C0219, SemVirtualDeg C0297, SemDeg C0269, SemDegFamilies C0284, SemPad C0280, SemAccept C0267, SemHonest C0270, SemAssembly C0161, SemDuplexDecoder C0322
- LogUpChain C0204, LogUpAssembly C0184, Extraction C0134, CircleSampler C0279, CopyInputLinks C0114
- MaskSource C0365, MaskProtocol C0320, MaskView C0332, MaskEarly C0400, MaskNoHit C0391, MaskBadSets C0348, MaskD2 C0334, MaskD2Glue C0376, MaskPrefix C0377, MaskSemantics C0349, MaskValue C0283, MaskDensity C0364, MaskDuplexDecoder C0335

Copies, all regular files:

- `LogUpFrac`, `MessageDescent` and `SemBadSets` were copied from `objs`. They do not depend on `R0P.Core`. `Zerocheck` and `Sumcheck` were already in the overlay, byte-identical to `objs`.
- The same directory-shadowing problem occurred once more, for `AspisR1CircleFallback`. I copied its three non-dependent siblings (`Types`, `Funs`, `FunsExternal`) from `objs` as regular files; `copied_nondep.txt` lists them. No dependent was ever copied.

## 6. Remaining blockers, by owner

There are 9,894 affected modules not yet rebuilt. Their labels in `HOST-REBUILD-ORDER.tsv`:

| Label | Modules |
| --- | --- |
| blocked: W3b + Stream C | 6,948 |
| blocked: W3b + devnet + Stream C | 2,418 |
| blocked: Stream C only | 416 |
| blocked: W3b only | 112 |

- **W3b.** The `NHG_*` serializer theorems, `WireBindingRecordCodec`, `RPz7_F3J_Public`, `RPz8_F3V_Public`, `PublicParserWork`, `PublicParserAllocationM10` and `PublicParsedIndexM10`. Everything downstream waits for them, including `NKR_DigestAssociation`, `NKR_DigestOptionalValue`, `RPv_FJq_PublicModel` (edited) and `RPv_FJn_ModelInputs`.
- **Stream C emission.**
  - `PublicExtractedRawBridge431` and `WithdrawalCarrierBridge431`. These need the PIN2 re-extraction of `r0::Public::public_bytes` with `private_public`/`withdrawal_public`, a `project` that copies pool, domain and destination, and a re-proof of `extracted_refines_core` against the new `PublicRawCore`. Their dependents include `ExtractedPublicCheckedBridge432` and `ExtractedAdapterStageBindingObligations`.
  - A PIN2 emission of the native crate `FIq_Native`, which replaces `PIN2_SemanticPublicStandIn`.
  - `RPv_FIz_CoefficientsOnRun` and `RPv_FIz_WideCoefficientsOnRun`. These state facts about the extracted `semantic_packed` run on the pre-PIN2 native `SemanticPublic`, so they need the PIN2 native function. They are where builder work ends and extracted-run association begins, and I did not edit them.
- **Devnet regeneration.** The 15 `NDO_JF*` fixture modules and everything downstream of them.

## 7. Import order for the host rebuild

`HOST-REBUILD-ORDER.tsv` is a topological order of all 10,592 affected modules: everything downstream of `R0P.Core`, `PublicRawCore` and `R1PublicSourceRaw`, plus the stand-in. Each row gives its status and source.

The host should first load W2's 27 objects and then this branch's 671 objects, in the order the file gives (rows marked `done-W2` / `done-W3a`). `R1PublicSourceRaw` and `R1PublicSourceRawMap` are labelled `done-W3a (supersedes W2)`: use the objects from compiles C0001 and C0003, not W2's.

After that, the host should build the blocked modules in the same file order as their owners land:

1. W3b's roots, then their dependents.
2. Stream C's `PublicExtractedRawBridge431` / `WithdrawalCarrierBridge431` (and the native-crate emission, which retires the stand-in), then their dependents.
3. The `NDO_JF*` regeneration, then its dependents.

Only then: one coherent cold replay of the full closure, one axioms audit of the two top theorems, and the ledger gate.

target not yet established
