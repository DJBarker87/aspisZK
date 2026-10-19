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

(2b pending)

## 3. Closest composed theorem

(pending)

## 4. Links shared with the privacy track

(pending)

## 5. Critical path

(pending)

## 6. What could not be determined

(pending)
