# R1 soundness gap map (2026-10-19)

Read-only analysis at base `ac486fac6` on branch
`codex/r1-soundness-gapmap-20261019`. No builds, no Lean attempts, no source
changes. Every theorem cited below was opened at the cited file:line in this
tree; a status note's claim is not repeated unless the named declaration was
found.

## 1. Target statement

**(T), as given.** For the deployed R1 two-transaction path (stage-1 verifier
transaction plus Pool settlement with nested stage 2), if both transactions
accept, a witness satisfying `Rspend` for the public statement can be
extracted, except with probability at most 2^-100 per proof attempt with no
grinding credit, in the query-dependent `Q·max_row + collision` form, under
named cryptographic and runtime premises.

**The deployed scope at this base.**
- Verifier: `programs/r1-cost-probe` and `crates/aspis-r1-cost-probe` at the
  CU-savings tip (candidate 14, `39c2971dd`; ten kept candidates 1-7, 10, 12, 14;
  `FINAL-RESULT.json`), features `pool-adapter,private-leaf-salts`. The measured
  ELF is `a70f30bd...`. `verifier.rs` has since changed: its sha256 is now
  `db70ae3d...` against `e65f4148...` in `FINAL-SOURCE-ADMISSION.json`. The
  privacy commits ad57ac42f..0d482eca6 added `cfg(feature = "prover")` error
  variants. LEAD-REVIEW-CU-BOUND-2 records the rebuilt ELF `4421aafd...`, whose
  `.text`/`.rodata` are identical to `a70f30bd...`. The other six admitted
  files match their admission hashes byte for byte.
- Pool: `programs/aspis-pool` after B1/B4 (`122c92ddd`; SBF `121f3e29...`).
  Under Decision 4 (LEAD-DECISIONS-20261015), the Pool's part in the
  soundness theorem is its binding of the public statement and the
  stage-2/checkpoint handoff. Nullifier freshness (Freshness-B1,
  MarkerSeedCR-224), lanes and custody are release gates outside (T).

**(T) restated against the Lean names that exist.** Fix a decoder `D` and
decision `d`, and let `P` be an adversary program in the lazy memoized byte
oracle (`AspisV8R19.MemoizedProgramLaw`). Let
`relation pub w := ∃ p, SemanticPublicWire.parsePublic pub.pubBytes = some p ∧
SpendRelation.Rspend p w` (`LiteralProtocol.lean:26`; `Rspend` at
`SpendRelation.lean:42`, with `AppendBinding` at `SpendAppendBinding.lean:17`
and the checker equivalence `check_eq_true_iff` at `SpendRelation.lean:85`).
(T) is then the conjunction of:

- **(T-model)** `lazyMean exp emptyTable failureMass ≤ kappa Q + N·B + δE`,
  where:
  - `exp` is the compiled experiment of `P` against the model verifier
    `RawCutProverCompiler.verifier D d` (`RawCutProverCompiler.lean:27`);
  - `failureMass run` is the probability over extractor coins that the run
    accepts and `RawRecordedPublicSpendExtractor.extract` returns `none`
    (`RawRecordedOracleExtractionMass.lean:44`);
  - `B = 15/2^109` (`PerAttemptEnvelope.lean:17`), with
    `33·B < 2^-100` (`thirty_three_B_lt`, `PerAttemptEnvelope.lean:54`);
  - `kappa Q = 12·Q²/2^256` (`RawAdaptiveDecoderInjection.lean:27`);
  - `δE = 2^-126` (bank abort; the Decision 3 allowance is 2^-120).

  A successful extraction is sound: it satisfies `relation`
  (`RawRecordedPublicSpendExtractor.returned_relation`,
  `RawRecordedPublicSpendExtractorReturnedRelation.lean:17`). `N` is the
  adversary's count of recognised decoded starts, which plays the role of
  `Q` in `Q·max_row`. `Q` is the first-read budget. Both stay symbolic, as
  Decision 4 and TARGET-CLARIFICATION require. Per attempt, `N ≤ 33` gives
  `< 2^-100` before the collision and abort terms.
- **(T-src)** The model verifier `RawCutProverCompiler.verifier D d`, the
  sampler `LiteralByteSampler.samp`, the decoder `D` and the public carrier
  `LiteralTranscript.Public` are refined by the deployed stage-1 + settlement
  pair. Both transactions accepting on bytes `(pub, proof)` implies the model
  verifier accepts the same statement under the same oracle, with the same
  first-read and decoded-start budgets.
- **(T-ext)** The extractor runs in expected polynomial time with failure
  `δE ≤ 2^-120` (Decision 3), and it reads only the run's first-read log.
- **(T-prem)** The named premises: ROM for the transcript/commitment hash,
  the Solana runtime and account-ownership premises of Decision 1, and the
  J1.R16 syscall semantics.

No single Lean theorem states (T-src). §3 names the closest composed theorem.

## 2. Links

The status vocabulary is the one fixed for this job. Owners are inferred from
commit messages and branch names; every commit is authored as `DJB8787`.
- **Codex** means the user's live Codex sessions committing directly on
  `research`, with "Prove/Derive/Bind/Connect..." subjects.
- **Lead** means the coordinating Claude session (lead reviews, decisions and
  inventories).
- **Lead-worker** means a lead-issued `codex/r1-*` worker branch.
- **Privacy** means the `codex/r1p-*` workers and the privacy LOG.

Sizes:
- S is about one focused module or a check.
- M is a multi-module bridge over existing extraction.
- L needs new extraction plus multi-module proof, or a whole-cone audit.

Paths are relative to `docs/research/100bit-spend-path-20261013/` unless
they start with `docs/`. Receipts are host `receipt.json` files under
`evidence/`. "Std axioms" means the receipt or log shows only
`[propext, Classical.choice, Quot.sound]`.

### 2a. Protocol model (Lean, idealised and compiled)

| id | link | status | evidence / cite | owner | deps | size |
|---|---|---|---|---|---|---|
| M1 | `Rspend` (Decision 1 relation, J1 `SpendRelation` + `AppendBinding`), plus executable checker | PROVED | `lean/SpendRelation.lean:42` (`Rspend`), `:85` (`check_eq_true_iff`); `lean/SpendAppendBinding.lean:17`; lead-accepted J1 (design/J1-RELATION-STATEMENT-20261015.md; evidence `lean-literal-protocol-20261015/`) | Codex, lead-accepted | none | S: done |
| M2 | Deterministic algebraic binding: γ joint list, κ, α₀, α₁ (with repeated lift), q22 containment, ρ | PROVED | `lean/ConcreteBinding.lean:58,67,74,84,97` (`gammaBad_card`, `kappaBad_card`, `firstBad_card`, `secondBad_card`, `binding`). Accepted in v8-r1-20261011/R1_SOUNDNESS.md "Consolidated status". A per-module host receipt was not located in this read (§6) | Codex; L1/L2 lead-workers | none | S: done |
| M3 | Round-by-round classifier for all 33 rows (S rows 0-24, circle 25-26, γ/κ/α₀/α₁ 27-30, q22 31, ρ 32): D1, D2 | PROVED | `lean/LiteralClassifier.lean:72` (`byte_density`); `lean/LiteralByteProtocol.lean` `d1`/`d2`; evidence `j1-literal-d2-lead-review-20261015.json` | Codex, lead-accepted | M2 | S: done |
| M4 | Per-attempt arithmetic: 33·B < 2^-100, B = 15/2^109; fresh-attempt hit mass | PROVED | `lean/PerAttemptEnvelope.lean:17,54`; `lean/LiteralFreshAttemptBound.lean:100` (`thirty_three_rows_lt`); receipt `concrete-literal-per-attempt-and-wire-20261016/LiteralFreshAttemptBound/` exit 0, std axioms | Codex | M3 | S: done |
| M5 | Terminal model implication: `Checks` + no classifier hit ⇒ `relation` (model D3) | PROVED | `lean/LiteralAcceptanceTerminal.lean:34` (`Checks`), `:87` (`checks_noHit_relation`), `:109` (`conditional_d3`) | Codex | M1, M2 | S: done |
| M6 | Adaptive membership FS bound `Q·maxErr + kappa Q` | PROVED (conditional) | `lean/RawAdaptiveMembershipBound.lean:56` (`membership_bound`; hypotheses `hQ`, `hformat`, `hterminal`); receipt `all-round-adaptive-decoder-and-bound-20261016/RawAdaptiveMembershipBound/` exit 0 | Codex | M3, M7 | S: done (superseded by M9 for (T)) |
| M7 | Merkle compiler (Decision 2 stage 2): compiled-run word stability; clean model derived from checked acceptance | PROVED | `lean/RawCompiledRunWordStabilityV8.lean:39`; `lean/RawChecksAdaptiveCleanModel.lean:125`; receipts `compiled-run-word-stability-20261019/`, `checked-acceptance-no-clean-model-premise-20261019/RawChecksAdaptiveCleanModel/` exit 0, std axioms | Codex | M5 | S: done |
| M8 | Recorded-run extractor: returns only `relation` witnesses; succeeds on checks + no hit + bank success; bank abort ≤ 2^-126 | PROVED | `lean/RawRecordedPublicSpendExtractorReturnedRelation.lean:17`; `lean/RawRecordedPublicSpendExtractorCompleteness.lean:22`; `lean/LiteralFreshBankAbortComposition.lean:28` (`bankAbortMass_le`); receipt `recorded-public-extractor-completeness-20261019/` exit 0 | Codex | M5 | S: done |
| M9 | Composed model failure bound `failureMass ≤ kappa Q + N·B + 2^-126` | PROVED (conditional) | `lean/RawChecksAdaptiveFailureNoModel.lean:34` (`checked_acceptance_failure_bound_no_model`); receipt `checked-acceptance-no-clean-model-premise-20261019/RawChecksAdaptiveFailureNoModel/receipt.json`: exit 0, 7.60 s, peak RSS 2,994,864,128 B, 0 swaps, std axioms (§3) | Codex (b3de2f610) | M6-M8 | S: done |
| M10 | Extractor efficiency (Decision 3): expected-polynomial field/hash-log/bit cost; δE ≤ 2^-120 in the stated cost model | OPEN | Components proved: GCD/division/mod-power cost mirrors, RR traversal and retry budgets (`lean/ActualCompPolyGCDCostMirror.lean`, `lean/ActualLongDivisionTotalCostV2.lean`, 5642782d0, c60124b28). The M9 README states that "full extractor bit-cost" remains | Codex | M8 | M: compose existing cost lemmas into one bound over the `extract` call graph |

### 2b. Deployed source to model (T-src)

| id | link | status | evidence / cite | owner | deps | size |
|---|---|---|---|---|---|---|
| R1 | Sampler correspondence, rows 0-24: actual initializer and first25 source calls under one logged oracle give the literal sampler prefix | PROVED (conditional on R10) | `lean/RawSourceGlobalOracleFull25.lean:33`, `lean/RawSourceLiteralFull25Prefix.lean:51`, `lean/RawSourceLiteralSamplerStep.lean` (a40d953d0, 971f32287, 294bf719e); report `evidence/source-global-oracle-full25-20261019/REPORT.md` (std axioms) | Codex | R10 | S: done; residual premise in R10 |
| R2 | Semantic finish on actual source: parsed semantic view, ten rounds, R0P mask and WideExact sumcheck chain (the `semanticChecks`/`claimParse`/`polynomialParse` fields of `Checks`) | PROVED (conditional on R3) | `lean/RawActualParsedFinishLiteralPrefix.lean:21` (`parsed_finish_literal_prefix`; receipt `actual-finish-literal-prefix-20261019/root-...-nuc-v2-20261019/` exit 0, std axioms); `lean/RawActualParsedFinishWideEndpoint.lean:26` | Codex | R3 | S: done; R3 owed |
| R3 | `FinishModel.Boundaries`: the explicit arithmetic, allocation, circle and root-conversion APIs of the finish model (terminal V4 composition, array loops, heap helpers) | OPEN | Components checked as isolated source **candidates**, not adopted production: `lean-candidates/current-terminal-*`, `named-heap-overwrite-helper-20261019`, `tx1-accumulator-overwrite-20261019`. SOURCE-PROOF-CU-INTERFACE-20261019.md says they are not the current production source. The circle extraction blocker is recorded at 450180974 | Codex | none | L: eight boundaries, two need source candidates adopted (CU re-run) |
| R4 | Sampler correspondence, rows 25-32 (circle 25-26, γ/κ/α₀/α₁ 27-30, queries 31, ρ 32), including reseed and nonzero-γ handling | OPEN | `lean/ExtractedPreparedReachability.lean:82` (`prepare_success`) derives the ordered opening calls 27..32 on the pre-CU `Prepared`. Query sampling is an explicit boundary there. Candidate 1 later changed `Prepared::new` (see S1). source-global-oracle REPORT lists "source rows 25-32" as remaining | Codex | S1, R10 | M |
| R5 | Public decoder: actual `decode_k`/field parsers equal the strict canonical decoded-wire parser | PROVED | `lean/ActualDecodeKStrictQM31Parser.lean:26` (`source_refines`), `lean/ActualDecodeKFieldParserTransport.lean:41` (2d934ef08, 3adb86d04, f8f57e1e7) | Codex | none | S: done |
| R6 | Actual caller input = decoder input; `publicParsed` from caller reachability; first-caller success | PROVED-STALE | `lean/ExtractedFirstCallerReachability.lean:82` (`first_success`) was proved before candidate 6, which re-emits `program::first` and adds `first_decoded` and a new adapter `stage1` binding (`evidence/cu-savings-20261019/candidate6/declaration-repin-inventory.json`) | Codex | S6 | M |
| R7 | Pool/adapter statement binding, withdrawal: `reconstruct_asq8_statement` success fixes pool, domain, anchor sequence/root, asset, lane | PROVED | `lean/ExtractedAdapterWithdrawalBindings.lean:206` (`reconstruct_withdrawal_bindings`), `:88`; focused check std axioms (design/J1-ASQ8-WITHDRAWAL-BINDINGS-20261016.txt) | Codex | P5, P6 | S: done |
| R8 | Pool/adapter statement binding, transfer variant | OPEN | No transfer counterpart of R7 in `lean/`. LEAD-CALLER-DECISIONS-20261016 item 3 says: "no automatic transfer to a payment/transfer caller" | Codex | R7 | M: mirror R7 over the transfer arm |
| R9 | Same statement across stages: serializer witness `hs` at the stage-1 caller, supplied-public `hbind`, and stage-2 reconstruction equal to the stage-1 serialized bytes | OPEN | J1-ASQ8-WITHDRAWAL-BINDINGS-20261016.txt: "Actual serializer success hs and the same-byte/checkpoint binding across stages remain OPEN, as does supplied-public hbind"; OPEN-PROOF-OBLIGATIONS-20261016 item 3 | Codex | R6, R7, R8, R13 | M |
| R10 | Global execution-log embedding: one consistent byte-oracle log contains every actual tx1 and tx2 digest call (source logging matches the ROM execution law) | OPEN | Explicit premise in R1/R11 (source-global-oracle-full25 and source-c2-causal-word REPORTs: "Actual global log containment and oracle consistency remain premises") | Codex | P3, R14 | M: derive from the digest-call traces once tx2 is extracted |
| R11 | Commitment words, C2: actual source C2 root determines one pre-commitment typed word; logged accepted openings project to it; row-2 literal constructor | PROVED (conditional on R10) | `lean/RawSourceC2WordBinding.lean:39,70`; `lean/RawSourceC2CutBinding.lean:52` (accepted-v2 receipt; superseded-v1 had `sorryAx` and exit 1); `lean/RawSourceC2LiteralMessage.lean:23`; receipts under `evidence/source-c2-causal-word-20261019/` exit 0, std axioms | Codex (5e641b58a, 0b97e23a0, cc74be164) | R10 | S: done |
| R12 | Commitment words, C1 (initial) and folded second commitment: source frames, roots, words | OPEN | source-c2-causal-word REPORT: "C1/folded commitment cuts ... remain" | Codex | R10, R13 | M: replicate R11 twice |
| R13 | Actual Merkle verification: leaf bytes, salts, domains, indices, path geometry, padding, accepted reads equal to the ideal path program | OPEN | Parent hash call and 257-byte preimage checked as a candidate only: `lean-candidates/current-merkle-path-20261019/RawMerkleParentCall.lean:52`, `RawMerkleParentBytes.lean:39` (9d12464cc). Not in the canonical root. The full path is uncommitted live work (§6) | Codex | R5 | M |
| R14 | Stage 2 execution: `verifier::tx2_authenticated`, `resume`, the remaining 12 queries and `finish_relation` (pairing, both fold equations, final value checks) | OPEN | No Aeneas extraction or Lean statement mentions `tx2_authenticated`, `resume` or `finish_relation` anywhere under `lean/`, `lean-candidates/` or `evidence/` (searched at this base). Source: `crates/aspis-r1-cost-probe/src/verifier.rs:332,379,450` | unassigned | S1-S9, R13, R15 | L: new extraction of the stage-2 cone, then its fields of `Checks` |
| R15 | Checkpoint authentication: tx1's checkpoint write and tx2's `resume` carry every value tx2 trusts; derived canonicality of skipped wide values | REFINEMENT-OWED | AUTHENTICATED-TX2.md (G_R1.3 covering argument and Rust tests; checksum unkeyed, so provenance rests on P2); 23 checkpoint tests (LEAD-REVIEW-J1-VERIFY-QUERY-C2-20261018) | Codex / lead-worker | P2, R14 | M |
| R16 | `hchecks`: deployed acceptance ⇒ every field of `LiteralAcceptanceTerminal.Checks` (public parse, matching/opening readers, pairing, query decode, `firstMatch`, ρ `residualBatch`, semantic) on the same transcript | OPEN | The hypothesis `hchecks` of M9 (`lean/RawChecksAdaptiveFailureNoModel.lean:42`). Fields are partially covered by R2 (semantic), R5 (parser) and the indexed query helper (`d189b9ac6`, evidence `batched-weights-generated-query-bidirectional-20261019`). No composition exists | Codex | R2-R15, R17, S1-S9 | L: the core remaining proof |
| R17 | Runtime fold and domain commutation: source `circle_fold`/`line_fold`/`QueryGeometry` equal the model `LineFold`/`storedFirstLineX18` geometry and D18 transport | OPEN | No Lean mentions `circle_fold`/`line_fold` source bodies; the R1_SOUNDNESS α₁ row leaves "runtime fold/domain commutation (Src)" open. Candidate 7 changed `QueryGeometry` | Codex | S7 | M |
| R18 | `htag` (initial transcript tag = 2) and commitment-message formats for the deployed transcript | OPEN | Explicit hypothesis `htag` of M9 (`lean/RawChecksAdaptiveFailureNoModel.lean:40`); formats partly derived (2892f6cfd, `lean/RawChecksInjectionFormat.lean`) | Codex | R1 | S |
| R19 | `hQ`, verifier half (QV): distinct first reads by stage 1 + stage 2 bounded for every admitted input, rejected inputs included (Decision 4) | REFINEMENT-OWED | Constants only: `lean/VerifierCallBudget.lean:55-60` (`stage1Budget 10 = 328` ... by `rfl`). `SourceSimulation.preservesPrefix` (`lean/VerifierPhaseCost.lean:235`) has no instance; its instantiation is OPEN (design/J1-R16-R19-RUNTIME-RELEASE-20261015.txt). The 583-call ordered trace is measured on fixtures | Codex | R14, R10 | M |
| R20 | Pool CPI handoff: the Pool passes the re-encoded ASQ8 request (B1 suffix stripped) and the authenticated accounts to nested stage 2 | REFINEMENT-OWED | LEAD-REVIEW-POOL-B1-20261019 ("verifier source and ELF untouched"); Pool suites 118/87/123/123 and mutation tests (evidence/pool-b1-20261019/) | lead-worker (codex/r1-pool-b1) | P5 | M: needs a Pool extraction; none exists for the B1 path |
| R21 | `verifier.rs` drift since admission: `cfg(feature = "prover")` error variants (ad57ac42f..) | REFINEMENT-OWED | Admission hash `e65f4148...` against current `db70ae3d...`. `.text`/`.rodata` identical, 39 bytes of panic-line data shifted (LEAD-REVIEW-CU-BOUND-2-20261019) | Privacy | none | S: confirm the not(prover) extraction is unchanged |

### 2c. Re-pins owed by source changes after the proofs

| id | link | status | evidence / cite | owner | deps | size |
|---|---|---|---|---|---|---|
| S1 | CU candidate 1 (reuse γ powers): `prepared_claim`, `Prepared::new`, `tx1_prepare`, `tx1` (10 declarations in the accepted Prepared/tx1 cones) | REPIN-OWED | `evidence/cu-savings-20261019/candidate1/declaration-repin-inventory.json` ("historical checked theorem is not evidence for optimized body") | Codex | S9 | M |
| S2 | Candidate 2 (opt-in profiling observer): `lib.rs`/adapter observer selection | REPIN-OWED | candidate2 inventory (`requires-repin-after-observer-selection-change`) | Codex | none | S |
| S3 | Candidate 3 (fixed S2 inactive groups): `weights::grouped_inactive_pair`, new `s2_grouped_inactive_pair` | REPIN-OWED | candidate3 inventory, obligation "all 1024 S2 classification bits agree with Variant::row and COPY_ACTIVE_ROW_MASKS". No proof found | Codex | none | M |
| S4 | Candidates 4 and 10 (delayed base-dot reduction; fixed 608-byte prefix): `fast_dots::four_dots` | REPIN-OWED | Mathematical batch bound proved: `lean/FastDotFoldedBatches.lean` (260755780; std axioms per `evidence/fastdot-folded-batches-20261019/README.md`). The README says it does not prove the "actual Rust loop-to-batch correspondence"; `four_dots` has no emitted body | Codex | none | M |
| S5 | Candidate 5 (private canonical dot operands): `fast_pairing::canonical::{Q::from_wide, Dot::new, Dot::push}`, `EbyKDot`, `EbyEDot` | REPIN-OWED | candidate5 inventory ("No admitted emitted Lean body for private fast_pairing kernels"). No proof found | Codex | none | M |
| S6 | Candidate 6 (reuse decoded public statement): `program::first`, new `first_decoded`, adapter `stage1` | REPIN-OWED | candidate6 inventory (re-emit `first` and its closures) | Codex | none | S |
| S7 | Candidate 7 (reuse query geometry): `QueryGeometry::for_range`, `accumulate`, `accumulate_with_node`, `query_with_geometry` | REPIN-OWED | candidate7 inventory | Codex | none | M |
| S8 | Candidate 12 (transaction-local ρ residues): `BatchedWeights::{new,push,value,finish}`, `accumulate*`, `query*`, `tx1_finish`, `tx2`, `tx2_authenticated` | REPIN-OWED | Arithmetic and part of the extraction proved: `lean/AspisR1BatchedAllPrefix.lean`, `AspisR1BatchedActualReducerFinish.lean` (efa2ddcec), `BatchedWeightsActualReducer.lean` (33ee22801), `BatchedWeightsNaturalRangeQueryGlobalV1.lean` (2f816c0f1), `lean/extracted-source-proof-loops-20261019/AspisR1BatchedWeightsExtraction/`. The README (`evidence/batched-rho-fold-source-bridges-20261019/`) says "Canonical input/field selection, Vec loop behavior and full caller/state source correspondence remain open" | Codex | R14 | M |
| S9 | Candidate 14 (factored S2 Libra row): `weights::factored_s2_libra_weights`, `Weights::pair` | REPIN-OWED | Identity proved: `lean/S2LibraFactoredIdentity.lean` (efa2ddcec; README: "not the complete optimized-verifier re-pin"; machine arithmetic and loop equivalence outside) | Codex | none | S |
| S10 | Digest32 migration and Decisions 1d-1h refactors: whole-cone declaration inventory regenerated at the final ref | REPIN-OWED | The inventory is pinned at `af828dec0` with verifier `a0c440c3...` (Decision 1c): 289 unchanged / 52 re-extracted / 1 replacement (design/J1-INTEGRATED-DECLARATION-REPIN-20261016.md). Since then come 1d/1e/1f unrolls, 1g, 1h (five targets re-extracted, LEAD-REVIEW-DECISION-1H-20261019) and S1-S9. OPEN-PROOF-OBLIGATIONS item 12: "the Digest32 migration's whole-cone inventory is not complete" | lead + Codex | S1-S9 | M: rerun `tools/j1-integrated-declaration-repin.py --require-complete` at the final ref, then fix the failures |

### 2d. Premises and final closure

| id | link | status | evidence / cite | owner | deps | size |
|---|---|---|---|---|---|---|
| P1 | Random oracle for SHA-256 as used by the Digest32 duplex, Merkle hashing and `sol_sha256` (the lazy memoized byte oracle of M6-M9) | PREMISE | docs/assumptions-ledger.md:36 (project ledger, V5 era, 2026-08-25). Used by Decision 2's probability route (LEAD-DECISIONS-20261015). OPEN-PROOF-OBLIGATIONS item 11 still requires it to be stated explicitly in the R1 theorem | user (ledger) / lead | none | S: restate for R1 |
| P2 | Solana runtime: account ownership and write permission; tx1 checkpoint account verifier-owned and written only by the tx1 path after strict parsing; proof bytes immutable after finalisation | PREMISE | LEAD-DECISIONS-20261015 Decision 1, "Trusted preconditions, stated as explicit assumptions" | user / lead | none | none |
| P3 | J1.R16 syscall semantics: `sol_sha256` = FIPS 180-4; `sol_create_program_address` = one SHA-256 with stored bump | PREMISE | design/J1-R16-R19-RUNTIME-RELEASE-20261015.txt:9-16. The release cluster observation is "PENDING" there | lead | none | S: record the cluster version at release |
| P4 | `R16ReadonlyMetadataProjection` (the observed account metadata equals the runtime's) | PREMISE | `lean/R16ReadonlyMetadataBoundary.lean:23`; named runtime premise in OPEN-PROOF-OBLIGATIONS item 3. Runtime backing: 13 mutations rejected and 2 controls pass on the 1h ELF (LEAD-REVIEW-CU-SAVINGS-20261019 item 3). Not re-run on `a70f30bd`/`4421aafd` | lead | none | S |
| P5 | F6: a stored bump or Pool-only hint authenticates the master, checkpoint, pages and vault accounts (B4) | PREMISE | design/POOL-B1-FRESHNESS-PREMISE.md §5; accepted in LEAD-REVIEW-POOL-B1-20261019 ("B4 and vault"); release formats in J1-R16-R19 (J1.R19) | lead | P3 | none |
| P6 | Charon/Aeneas/Lean/mathlib translate and check the recorded sources correctly | PREMISE | docs/assumptions-ledger.md:41 (V5-era ledger). No R1-specific acceptance was found in the R1 design notes | user (ledger) | none | S: restate for R1 |
| P7 | Rust/LLVM/platform-tools/SBF build correctness, so the deployed ELF has the reviewed source's semantics | PREMISE | docs/assumptions-ledger.md:42 (V5-era ledger; there it rests on byte-for-byte SBF reproduction) | user (ledger) | none | none |
| C1 | Artifact pin: one final SBF artifact, features and toolchain bound to the theorem's source scope, reproduced | OPEN | OPEN-PROOF-OBLIGATIONS item 12. ELFs `a70f30bd` (measured) and `4421aafd` (rebuilt) differ in `.data.rel.ro` | lead | S10, R21 | S |
| C2 | Unified build: soundness roots in one coherent manifest, then one frozen-manifest replay with axioms audit (AGENTS.md cadence) | OPEN | `evidence/cu-savings-20261019/FINAL-RESULT.json` (`soundness_manifest`: 718 sources, 0 conflicts, `compile_started: false`); privacy LOG D63.2/D71 (manifest 2 is privacy-only) | lead | every PROVED row | M: compute-bound and mechanical |
| C3 | Final quantitative theorem: instantiate (T-src) premises into M9, add the δE ≤ 2^-120 allowance and state P1-P7 explicitly | OPEN | OPEN-PROOF-OBLIGATIONS item 11. No such theorem exists | Codex / lead | M9, M10, R16, R19, R9, P1-P7 | S once its inputs exist |
| X1 | Freshness-B1 and MarkerSeedCR-224 (nullifier marker uniqueness; blocking only) | PREMISE | design/POOL-B1-FRESHNESS-PREMISE.md §2-3; named, "not proved" (LEAD-REVIEW-POOL-B1-20261019 Remaining). **Outside (T)** under Decision 4 (settlement release gate) | lead-worker | P3 | n/a for (T) |

**Counts (all 52 rows above, X1 included):**

| status | count | rows |
|---|---|---|
| PROVED | 14 | M1-M9 (M6 and M9 conditional on their stated hypotheses), R1, R2, R5, R7, R11 (R1, R2, R11 carry the explicit R3/R10 premises) |
| PROVED-STALE | 1 | R6 |
| REPIN-OWED | 10 | S1-S10 |
| REFINEMENT-OWED | 4 | R15, R19, R20, R21 |
| OPEN | 15 | M10, R3, R4, R8, R9, R10, R12, R13, R14, R16, R17, R18, C1, C2, C3 |
| PREMISE | 8 | P1-P7, X1 (X1 outside (T)) |

R2 and R11 are PROVED on source that predates candidates 1, 7 and 12, but
none of those three changed the functions R2 and R11 extract (`begin`,
the semantic rounds, the C2 frame). This was checked only against the
candidate inventories' changed-function lists.

## 3. Closest composed theorem

**`AspisR1.RawChecksAdaptiveFailureNoModel.checked_acceptance_failure_bound_no_model`**
(`lean/RawChecksAdaptiveFailureNoModel.lean:34`, commit b3de2f610).
Receipt: `evidence/checked-acceptance-no-clean-model-premise-20261019/RawChecksAdaptiveFailureNoModel/receipt.json`.
It records exit 0, 7.60 s wall and peak RSS 2,994,864,128 B, with 0
swaps. The log `lean.log` prints `[propext, Classical.choice, Quot.sound]`.
This is a focused check, not a frozen-manifest replay (C2).

**Conclusion.** `lazyMean (AcceptedAdaptiveFiatShamir.experiment (compiled D
d (buildWords D) P) (verifier D d)) emptyTable failureMass ≤ kappa Q + N·B +
2^-126`. In words: under the lazy random oracle, the probability that the
model verifier accepts and the recorded-run extractor fails is bounded by
`12Q²/2^256 + N·15/2^109 + 2^-126`. A successful extraction satisfies
`relation` (M8). This is the (T-model) half of §1, in the
`Q·max_row + collision` form, with the knowledge extractor built in. It is
the only theorem found that joins classifier density, the collision charge,
the Merkle compiler and the extractor, and that has no clean-model premise.
Its predecessor `RawAdaptiveMembershipBound.membership_bound`
(`lean/RawAdaptiveMembershipBound.lean:56`) is membership-only and still
takes `hformat` and `hterminal`.

**Parameters, universally quantified:**
- `decoder : LiteralByteProtocol.Decoder`, the row decoder;
- `d : ErasedPrefix → ErasedMessage → Bool`, the verifier's terminal
  decision, which is a pure Boolean over the erased transcript;
- `P : Prover`, the adversary program;
- `Q N : Nat`.

**Hypotheses** (lines of `RawChecksAdaptiveFailureNoModel.lean`):
1. `hQ` (:38). For every oracle `H`, the distinct first reads of the
   original experiment, prover and verifier together, are at most `Q`. The
   adversary half stays symbolic. The verifier half is R19 (QV for all
   inputs), which is REFINEMENT-OWED.
2. `htag` (:40). The run's public statement carries transcript tag 2. This
   is R18, OPEN, though it should be a small lemma about the deployed
   initializer.
3. `hchecks` (:42). Model acceptance under `d` implies
   `LiteralAcceptanceTerminal.Checks` on the compiled run's 33-round
   transcript. This is R16, OPEN, and it is the core of (T-src). Since `d`
   is free, `hchecks` is also where `d` must be shown to be the deployed
   decision.
4. `hN` (:55). The recognised decoded-start count of the compiled
   experiment is at most `N`. This is adversary-side accounting. It is a
   parameter of the statement, not a gap: per attempt `N = 33` gives
   `33·B < 2^-100` (M4).

**What it does not say.** It is a theorem about the Lean model verifier
`FS2.verifier (LiteralByteProtocol.protocol decoder) (decisionOnBytes d)`
(`lean/RawCutProverCompiler.lean:27`), not about the deployed program. It
does not mention stage 2, the checkpoint, the Pool or the ELF. Nothing
connects "the stage-1 and settlement transactions accept" to "the model
verifier accepts", and that connection is not a hypothesis either. To reach
(T), a further theorem must:
- simulate the deployed pair of transactions as this model verifier for a
  specific `decoder`/`d` (R1, R4, R10, R14, R15, R20);
- discharge `hchecks`, `htag` and the QV half of `hQ` for that
  instantiation;
- bound extractor running time (M10);
- name P1-P7.

Of the hypotheses, only `hN` and the adversary half of `hQ` are acceptable
as they stand.

## 4. Links shared with the privacy track

(pending)

## 5. Critical path

(pending)

## 6. What could not be determined

(pending)
