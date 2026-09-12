# File map and per-module status

**Every new Lean file is NOT COMPILED.** The descriptions below are intended claims of proof attempts, not checked results.
Generic consumers deliberately retain their premises and do not close their source-producer obligations.

| Lean module | Workstream | Intended first attempt |
| --- | --- | --- |
| `AdaptiveHazard` | FS/probability | Inductive history-dependent kernel hazard bound from per-state local bounds. |
| `AuthenticationBudget` | FS/authentication | Birthday/target arithmetic and union accounting; concrete event producers required. |
| `CausalPrograms` | FS/causality | Finite adaptive-program interpreter and prefix-run agreement. |
| `CheckedCandidate` | Extraction | Executable bounded search correctness/completeness for an available candidate list. |
| `ChronologicalPrefixes` | FS/causality | List-prefix cuts and unavailable-future noninterference primitives. |
| `CommonSupport` | Extraction | Common error support and union/pole combinatorics. |
| `CostTrace` | Resources | Trace cost arithmetic given calibrated source counters. |
| `DecoderUniqueness` | Extraction | Hamming triangle and conditional code-distance uniqueness. |
| `DigestProjection` | FS/authentication | Prefix/tail cardinality and truncation accounting; byte bijection still requires source binding. |
| `DistinctPair` | FS/samplers | Ordered distinct-pair cardinality and conditional joint-mass consumer. |
| `DistinctQueries` | FS/samplers | Distinct-query recurrence and per-factor upper bound; actual sampler law separate. |
| `FiatShamirTransport` | FS/conditional consumer | Explicit coupling/exception game-hop and adaptive trial consumer; NOT an Aspis FS theorem. |
| `FiniteMass` | FS/probability | Finite rational mass, monotonicity and union bounds; conditional transport helper. |
| `FirstExposure` | FS/causality | First query occurrence and prefix-fixed target obligations. |
| `ForkReplay` | FS/extraction | Replay/coherent-group/cost helpers; no useful-fork production bound. |
| `GaoInvariant` | Extraction | Euclidean Bezout step and candidate sample agreement outside locator roots. |
| `GlobalLedger` | Conditional consumer | Finite event composition and rational threshold; real partition/extraction producers absent. |
| `LazyROHazard` | FS/reference machine | Lazy-cache reference machine and fresh-answer hazard; no actual-source coupling. |
| `MaskTranslation` | ZK/static helper | Static additive mask translation/bijection, NOT full adaptive-view ZK. |
| `OracleCache` | FS/reference machine | Pure cache update and cache-hit coin irrelevance. |
| `PaymentTransition` | Payment slice | Small deterministic transition and replay prevention, NOT full forest/Token settlement. |
| `RejectionKernel` | FS/samplers | Bounded retry atom, equal atoms and retained abort mass. |
| `SelectedArithmetic` | Arithmetic diagnostic | Exact pinned constants and conservative reported residual/retry diagnostics. |
| `TransferAmounts` | Payment slice | Integer no-wraparound, positivity/conservation algebra. |
| `UniformStep` | FS/probability | Uniform finite-answer atom and target-set mass. |
| `UnresolvedTargets` | FS/authentication | Whole-domain phase resolver target-set cardinality, avoiding postselected targets. |

## Executable reference modules

The Python tests were executed; these remain reference algorithms and diagnostics, not production proof or SBF execution.

- `aspis_completion/cost.py`: Arithmetic upper-envelope calculator, never a calibrated CU theorem.
- `aspis_completion/extraction.py`: Bounded candidate-validation wrapper; does not assume candidates exist. Accepted output is backed by an independently supplied deterministic validator. Completeness, source authentication and permitted candidate production must be proved separately. This wrapper must never be counted as their proof.
- `aspis_completion/finite_rom.py`: Exact finite-ROM experiment interpreter (tiny alphabets only). Enumerates fresh answers uniformly. Repeated inputs reuse cached answers. A bad-answer target is evaluated from the PRE-answer history. This is a reference semantics and regression suite, not the actual Fiat--Shamir lift.
- `aspis_completion/forks.py`: Replay collector with explicit total work and coherent-prefix grouping. No useful-fork probability is assumed. Refusing/censored/incoherent branches are retained in the result instead of disappearing from a success denominator.
- `aspis_completion/gao.py`: Quadratic-time prime-field Gao reference decoder with checked output. Still not the selected circle/QM31 extractor. Unlike the Gaussian reference, this is a practical algorithmic starting point for larger samples; profile basis conversion and allowed authenticated sample production stay outside.
- `aspis_completion/masking.py`: Finite linear-mask diagnostics, not a full-view adaptive ZK simulator.
- `aspis_completion/oracle.py`: Instrumented classical lazy oracle and permitted-prefix access. The answer generator is external. Test RNG answers emulate a finite ROM; SHA256 answers can check concrete replay but are not evidence of randomness. Role labels are metadata and are NEVER prepended to the actual hash input.
- `aspis_completion/polynomial.py`: Exact prime-field polynomial and Berlekamp--Welch reference decoder. This is NOT the Aspis circle/QM31 decoder. It is an executable algebra/control oracle for decoder testing. The deployed field, basis, degree, evaluation-point and circle/GRS transformation refinements remain explicit integration tasks.
- `aspis_completion/query_sampling.py`: Exact ordered sampling-without-replacement arithmetic; source sampler not yet bound.
- `aspis_completion/sampling.py`: Exact finite decoder/retry distributions; no conditioning away aborts. This is a sampler-analysis library. It intentionally requires the source's raw decoder as input instead of guessing Aspis's SHA-to-field mapping.
- `aspis_completion/security.py`: Exact classical-ROM accounting with fail-closed unknown terms. No default global security claim. In particular, a per-prefix residual term cannot be applied after unrestricted Fiat--Shamir retries without a proved source coupling/trial-accounting theorem.
- `aspis_completion/trace_schema.py`: Validate instrumented evidence without inventing protocol domain separation. A trace receipt must contain the literal input bytes supplied to SHA. Semantic roles, encoded argument boundaries and producer ordinals are evidence metadata; they do not change the byte stream or prove it matches the Rust implementation.
- `aspis_completion/wire.py`: Pinned selected-q22 wire projection; no cryptographic acceptance claim. Layout cross-checked against SelectedWireBytes/PackedQueryRecord at 30a303a. This parser deliberately binds each projection to ONE immutable body. A local repaired profile must be reconciled before using it as an implementation oracle.

## Integration and validation

`integration/InspectPinnedEndpoints.lean` inspects the old remote interface; it is NOT the completed local repair and is NOT an integration proof.
`integration/README.md` states the required actual-source producers. `PROMPT.md` is the full agent task.
`tools/import_manifest.py` resolves explicit first-party source variants. `tools/lean_build.py` builds this pack only in a fresh directory.
`tools/kernel_replay.py` requests fresh replay but cannot prove the intended theorem is adequate.
`rust/src/lib.rs` is a reference parser/Merkle/trace crate with five unexecuted Rust test functions.

## Historical debug record

A retained failed Python attempt had an incorrect interpolation expectation. The expected coefficients were corrected from `[1,1,4]` to `[1,2,3]` for the stated samples; the decoder was not changed to accommodate the test. Final logs supersede that attempt.

## Completion boundaries

No compiled Aspis execution-to-model producer, complete classical FS theorem, selected QM31/circle extractor, full payment-witness theorem, global 100-bit theorem, adaptive ZK theorem or all-reachable CU certificate is claimed by this package. Those all have concrete tasks and supporting first attempts here.
