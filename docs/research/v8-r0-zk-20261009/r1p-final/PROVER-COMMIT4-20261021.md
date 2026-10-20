# Prover commitment continuation 4 — 2026-10-21

Branch `codex/cx-prover-commit4-20261021`, based on `8c69254eb`.
**The shared-oracle component route is checked; the nine complete source
checklist rows are not discharged.** A zero-filled redundant H1 tape
coordinate obstructs equal fibres on the existing full tape carrier.

D92 identifies the byte callback with the model oracle. No SHA-256 property
is assumed or proved. Evidence is collected under
`docs/research/100bit-spend-path-20261013/evidence/prover-commit4-20261021/`.

## Stage 1: shared oracle harnesses

Proof-only modules use one memoised table for both sides, keyed by the
concatenation of hashv slices. New points receive arbitrary 32-byte answers;
repeats receive the stored answer. Collisions remain possible. Capacity and
per-harness query budgets are assertions, not assumptions. Every accepted harness has an explicit unwind bound and enabled unwinding
assertions. The initial legacy-output runs are diagnostic only; final
structured-output function checks passed.

## Checklist scope

No complete source row is discharged by the component checks below. The
verbatim before/after inventory is retained at the end.

## Stage 2: oracle-parametric Lean refinement

New module `R1Z.ProverCommitOracleRefinement` proves cache evaluation,
cache extension, arbitrary fresh-answer extension, and the extracted mask
block, source block and private-leaf evaluations for **every** byte oracle.
The oracle is a function of concatenated bytes. The cache extension theorem
permits collisions. No SHA-256 property, independent-word law or source
carrier instance is inferred.

Env J attempt 8144: exit 0, wall 2.24 s, peak RSS 4,015,488 KiB, zero swaps.
All six `#print axioms` lines are in `lean/out-8144.log`: cache theorems use
`[propext]`, extracted callback refinements use
`[propext, Classical.choice, Quot.sound]`. Source SHA, dependency fingerprint,
revision and complete resource/audit receipts are in `lean/attempts.jsonl`.
The existing capped launcher was used, with no shared module overwritten.

## Stage 3: owned reference lowering and final axioms audit

The proof-only `prover_commit_reference` module is enabled by `cfg(kani)` or
`cfg(aeneas_ref)`. It has an owned expander state, byte-exact word extraction
and a 16-try sampler carrying its result. The first reference failed Aeneas's
nested-return prepass (`Option` language-item diagnostic); the carried-result
replacement translates successfully. Both Charon lowerings have
`has_errors=false`; only the successful replacement is adopted. The accepted
LLBC SHA and size are recorded in `reference-llbc.json`. The only external
constant is M31's exact `P = 2147483647`, defined rather than axiomatized.

The three generated modules compile separately in env J 8148–8150. The
scoped discriminant expansion follows the previous continuation and avoids
its global instance-name collision; raw constructor order and 0–4 values
are preserved. New `ProverCommitReferenceSource` proves cached reads ignore
the callback, termination at 16 attempts, and preservation after success
(attempt 8151). These are component properties, not a full tape theorem.

Final audit `R1Z.ProverCommitOracleAudit`, env J **8152**: exit 0, **2.37 s**,
**4,028,280 KiB** peak RSS, **0 swaps**. Its twelve complete axiom lines cover
all eleven new theorems and `privacy_R1_protocol`. Only
`propext`, `Classical.choice`, and `Quot.sound` occur. Attempts 8145/8146 are
rejected proof drafts with a constructor elaboration error; their recovery
`sorryAx` output is not accepted. Final salt refinement passes in 8147.
No existing privacy/source-identification/history module was edited.

## Stage 4: final shipped-source ELF gate

All shipped-file additions are proof-only; no production function was
changed. The Rust source revision for this first gate is `b5406a591`; the final
callback-route guard is covered by the later gate below. Rebuilt in this job's
own host workspace using the retained cache, Solana 3.1.13/platform-tools
v1.52, locked offline dependencies, four jobs and the frozen feature sets.
Native RUSTFLAGS is `-C link-arg=-Wl,--threads=4`; the freeze recipe unsets it
only for SBF and uses `-C link-arg=--threads=4` as the target-specific flag.
Every build scope has MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64. Reservation holds were respected. Time was expected in
incremental optimized compilation/linking, with no arithmetic gate.

| Program | SHA256 | Exit | Wall s | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| default | `dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34` | 0 | 41.233 | 648668 | 0 |
| devnet | `fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78` | 0 | 3.713 | 204192 | 0 |
| pool | `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` | 0 | 34.048 | 645152 | 0 |

All three pass `cmp --silent` against the preceding continuation's frozen
artifacts. `frozen-elf-check.json` contains exact commands, sizes, source
hashes and resource receipts; `#print axioms` is N/A for these Rust builds.
The SBF diagnostics remain in the logs; byte identity is the claimed gate.
Runtime suites were not repeated for cfg-only additions. No account/wallet transactions, deployments, peer worktree changes, or push
were performed. The three SBF-generated program key files remain on the
host at mode 0600; their private contents were not read and no key cleanup
was attempted (`key-retention.json`).

## Stage 5: exact ROM specialization and zero-fill obstruction

`mask_block_rom` and `source_block_rom` quantify over the actual
`R1Z.RomFiniteBin.Address bound → OracleAnswer` table and use its `lookup`.
The answer-carrier adapter is an explicit data parameter; no byte/digest
bijection or source carrier is smuggled into the result. Env J 8153 passes.

The actual `Tape K F` contains `AffCoordinate = (Fin 10 × Fin 1024) ⊕
(Fin 3 × Fin 1024 × Fin 4)`. Thus H1 has 1024 × 4 raw ideal coordinates,
even though `state_only_hiding.rs` samples H1 only when the row is inactive
and not the dependent row. The raw dependent coordinate is subsequently
ignored by the model's `balance 0`; all raw coordinates remain in the tape
carrier and in `R_commit_equal_fibres`'s quantifier.

New `ProverCommitFibreScope.zero_fill_not_equal_fibres`, checked against that
actual tape type, proves: if a decoder has any success and fixes raw H1
lane 1 / row 0 / limb 0 to zero on every success, then **no** common fibre
cardinality exists over all tapes. The tape with that coordinate equal to
one has an empty fibre, while the successful tape has a nonempty fibre.
The proof is symbolic; it never enumerates the tape or input carrier.
Env J **8156**: exit 0, 1.92 s, peak 3,511,324 KiB, zero swap, standard axioms.
Draft 8155 failed on decidability/membership elaboration and is rejected.

This rules out a direct adapter that zero-fills unused ideal coordinates.
It does **not** prove every possible completion impossible, nor that the
existing conditional privacy theorem is false. A completion must supply
those coordinates with the required exact fibre law and reconcile its
success/failure classification with the shipped sampler; alternatively a
new quotient-tape endpoint must transport the existing model proof. Neither
construction is supplied here. D92 callback equality alone supplies neither.
No zero-filled `tapeOf`, assumed cF, reserved-secret law, or source prover
instance is installed to paper over this obstruction.

The final audit after these source additions is env J **8157**: exit 0,
**1.89 s**, peak **4,028,480 KiB**, zero swap. Its fifteen full axiom lines
cover all fourteen new theorems and the unchanged protocol endpoint; all
are subsets of `[propext, Classical.choice, Quot.sound]`. Attempts 8152 and
8154 are earlier successful audits, superseded after identified source
additions, not unchanged full replays.

A final Kani guard checks that `HOST_HASH` through the actual function pointer
increments the shared table's call counter and creates exactly one cached
point for a repeated input. It passes; this detects an ignored pointer stub.
That proof-only addition is committed at `8517407c1`. All three ELFs were
rebuilt again from this final Rust revision and match the same pins and
retained frozen artifacts (`cmp`); see `frozen-elf-final-check.json`.

## Verbatim checklist before / after

The original `PRIVACY-FINAL-20261020.md` is unchanged. The following are the
nine complete source rows, rather than the nine successful function harnesses.
`checklist-before-after.json` records their checklist SHA and explicit
`discharged=false` flags.

Before (verbatim):

```text
| R_commit_D80.roots/nodes | AddressAt for all three roots/internal binary parents, child order, padded folded geometry, byte carrier and D81 grammar. Do not substitute eight-way C2 recovery for binary recovery. |
| R_commit_D80.leaves | Exact 0x71/0xf1/0x72 tags, packed leafVal/trailing salt, private-leaf backend and byte/digest conversions, on the actual prover tree. |
| R_commit_D80.bindings | Both secret-attempt binding reads, source/public/variant mapping, context encoding and digest answers (P`R1Z/LayoutR1PBin.lean:133`). |
| R_commit_D80.seeds | All three seed derivations, reserved secret distribution and source/D stream selection (P`R1Z/LayoutR1PBin.lean:136`). |
| R_commit_D80.salts | Full per-leaf secret salt derivation, nonce/tree/secret binding and LE32(u) (P`R1Z/LayoutR1PBin.lean:140`); verifier facts only consume disclosed salts. |
| R_commit_D80.mask_expander/source_expander | Stream/domain/seed/LE64(counter), eight words per block, no counter reuse, index/stream selection and complete hash-read coverage (P`R1Z/LayoutR1PBin.lean:131`). |
| R_commit_equal_fibres, cF | Exact equal-cardinality successful tape fibres for every τ. Deterministic expansion and successful tests do not establish uniform tapes. |
| R_commit_exhaustion | Every tapeOf failure implies one of the actual two 16-try little-endian stream-exhaustion events; exact source wordsE transport (P`R1Z/FinalR1PBin.lean:44,54`). |
| R_commit_counter₁/₂, R_commit_stream₁/₂, R_commit_cell_count, R_commit_blocks₁/₂ | E≤2^64, 16L≤8E, RCommitCount cell bounds and E≤2L; universal source commitment read completeness. D76's fixture count alone is not this universal refinement. |
```

After (verbatim, retained open):

```text
| R_commit_D80.roots/nodes | AddressAt for all three roots/internal binary parents, child order, padded folded geometry, byte carrier and D81 grammar. Do not substitute eight-way C2 recovery for binary recovery. |
| R_commit_D80.leaves | Exact 0x71/0xf1/0x72 tags, packed leafVal/trailing salt, private-leaf backend and byte/digest conversions, on the actual prover tree. |
| R_commit_D80.bindings | Both secret-attempt binding reads, source/public/variant mapping, context encoding and digest answers (P`R1Z/LayoutR1PBin.lean:133`). |
| R_commit_D80.seeds | All three seed derivations, reserved secret distribution and source/D stream selection (P`R1Z/LayoutR1PBin.lean:136`). |
| R_commit_D80.salts | Full per-leaf secret salt derivation, nonce/tree/secret binding and LE32(u) (P`R1Z/LayoutR1PBin.lean:140`); verifier facts only consume disclosed salts. |
| R_commit_D80.mask_expander/source_expander | Stream/domain/seed/LE64(counter), eight words per block, no counter reuse, index/stream selection and complete hash-read coverage (P`R1Z/LayoutR1PBin.lean:131`). |
| R_commit_equal_fibres, cF | Exact equal-cardinality successful tape fibres for every τ. Deterministic expansion and successful tests do not establish uniform tapes. |
| R_commit_exhaustion | Every tapeOf failure implies one of the actual two 16-try little-endian stream-exhaustion events; exact source wordsE transport (P`R1Z/FinalR1PBin.lean:44,54`). |
| R_commit_counter₁/₂, R_commit_stream₁/₂, R_commit_cell_count, R_commit_blocks₁/₂ | E≤2^64, 16L≤8E, RCommitCount cell bounds and E≤2L; universal source commitment read completeness. D76's fixture count alone is not this universal refinement. |
```

The component frontier is precise:

- Roots/nodes: no complete tree-construction or padded-geometry source join.
- Leaves: the actual private-leaf function agrees with independent byte
  concatenation for C1/0x71 (416 bytes), C2/0xf1 (192), and folded/0x72 (128).
  Actual packed `Pr.leafVal` and tree caller coverage remain unconstructed.
- Bindings: Pool private-attempt binding is checked, including independent
  81-byte context encoding and descriptor. The earlier public precommit
  binding and the source/public/variant mapping remain separate.
- Seeds: arbitrary-oracle block refinement supplies no OS/reservation law,
  full three-seed caller identification, or source/D stream-selection theorem.
- Salts: the actual valid forest-context leaf-salt method agrees with its
  independent two-hash reference for arbitrary nonce/binding/secret/tag/index.
  The complete per-tree caller loops and `Pr.caddr` carrier remain separate.
- Expanders: both block helpers and every valid local word slot are checked,
  including counter wrap, LE32 return, block/counter/seed/slot state. This
  is not a global non-reuse or complete-read/count certificate.
- Equal fibres: the direct zero-fill adapter is ruled out by the checked
  theorem above. A different successful full-tape completion or quotient
  construction, with a real source coupling, is still required.
- Exhaustion: the scalar/reference facts do not construct the source
  `tapeOf`, its failure classification or `wordsE` transport.
- Counts/budgets: no universal source caller/read-completeness instance is
  obtained from local wrapping arithmetic or the finite harness query budgets.

No `stub_verified` annotation is installed: the proved relational callees
are harness results, not Kani function contracts suitable for verified
summary substitution. Pretending otherwise would leave the caller proof
without an established contract. Direct full scalar comparisons are recorded
separately below, including any timeout; none can replace the tape laws.

## Final Kani results and stopping frontier

Eleven focused harnesses pass. Both sides use the same memoised oracle;
no reset occurs between sides. The finite table has four entries, with
asserted per-harness call budgets (2 for the function checks, 3 for the
regrouping check, 4 for the two-hash salt check; 6 conservatively for the
unresolved scalar comparisons). No capacity assertion is assumed away.
All accepted runs use explicit `#[kani::unwind(514)]` and
`--cbmc-args --unwinding-assertions`. Exact full targets/commands, source
snapshots, resource limits and tool-output logs are in the receipt directories
and matching `*-inputs.json` files. Kani `#print axioms`: N/A.

| Receipt / target | Exit | Wall s | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
| `oracle-v3` | 0 | 39.171 | 716580 | 0 |
| `callback-v1` | 0 | 18.53 | 807252 | 0 |
| `mask_block-v1` | 0 | 23.039 | 561140 | 0 |
| `source_block-v1` | 0 | 21.867 | 579488 | 0 |
| `mask_next_word-v1` | 0 | 41.201 | 1560536 | 0 |
| `source_next_word-v1` | 0 | 46.073 | 596692 | 0 |
| `pool_binding-v1` | 0 | 135.445 | 1677528 | 0 |
| `pool_leaf_salt-v1` | 0 | 337.862 | 2013148 | 0 |
| `private_leaf_c1-v1` | 0 | 175.394 | 2593196 | 0 |
| `private_leaf_c2-v1` | 0 | 65.236 | 1397692 | 0 |
| `private_leaf_folded-v1` | 0 | 44.439 | 1055660 | 0 |
| `mask_limb-v1` | 124 | 600.002 | unavailable† | 0 |
| `source_limb-v1` | 124 | 600.002 | unavailable† | 0 |

† Both direct scalar comparisons stop at the 600-second timeout, exit 124,
without a proof or counterexample. They were not rerun, and no cap or timeout
was raised. The timeout wrapper's reported 15 MiB RSS omits killed-child
rusage; it is not the CBMC peak. Kernel cgroup memory peaks are
4,133,142,528 bytes (mask) and 4,348,395,520 bytes (source), below the cap.
The attached two-second source sampler measured aggregate child RSS up to
4,189,048 KiB; this is a sampled peak, not an exact high-water mark.
`*-timeout-resource-note.json` and `source_limb-v1/rss-samples.json` preserve
these distinctions. Neither incomplete scalar check is release evidence.
The expensive step was bounded CBMC symbolic unrolling of the 16-try
sampler and shared cache, not SHA-256 or unoptimized finite-field arithmetic.
The next proof step is an established step contract/inductive sampler
refinement; the successful word-transition checks alone are not that contract.

Oracle-v1 was stopped to replace a variable-length cache search by a fixed
four-entry search and add explicit unwinding assertions; it is excluded.
Oracle-v2 used legacy output, which reported reachable instrumentation probes
as failures even though the functional assertions passed; the structured
v3 result is the accepted evidence. No property is claimed from either
failed diagnostic run. The two smaller builder references remain distinct:
this packet's scalar reference translates; the full builder lowering and
actual source/tape/carrier/caller construction from the previous report are
not repaired merely by this scalar result.

**Stopping result: the requested nine-row discharge is incomplete.**
The zero-fill route has a checked mathematical obstruction, and the two
full scalar comparisons have a demonstrated bounded backend obstruction.
A valid full-tape completion (or a quotient-tape endpoint), successful-source
exhaustion law, verified scalar composition, complete builder/caller/packing
identification, secret law and universal read/count transport still remain.
No complete row or unconditional source privacy statement is claimed.

All fourteen new top theorems and the unchanged endpoint pass the final
8157 axioms audit. Source revisions/SHA/dependency fingerprints and rejected
drafts are in `lean/attempts.jsonl`; the intermediate 8154 working-tree audit
snapshot is retained explicitly. `source-release.json` pins the adopted
source. `harness/validate.py` validates the retained packet without rerunning
any proof/build. `branch-log.txt` records the requested base-to-source-stage
commit history; the final evidence-only commit follows that snapshot.
No full frozen-manifest, adversarial or runtime suite was replayed unchanged.
All work is committed on the assigned branch; no push or peer-file edit.
