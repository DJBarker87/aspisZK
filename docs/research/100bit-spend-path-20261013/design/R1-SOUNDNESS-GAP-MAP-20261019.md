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

(pending)

## 3. Closest composed theorem

(pending)

## 4. Links shared with the privacy track

(pending)

## 5. Critical path

(pending)

## 6. What could not be determined

(pending)
