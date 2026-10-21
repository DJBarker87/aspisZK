# Prover commitment continuation 8 — 2026-10-21

Branch `codex/cx-prover-commit8-20261021`, base `a9a27745b`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit8-20261021/`.

## Stage 1: symbolic step replacement

The three 600-second comparisons from continuation 7 are not rerun.
The replacement separates scalar transitions, four-coordinate control flow,
and one balancing row from finite iteration. Results and limitations follow
with the accepted receipts. The scalar-step contract passes (16.839 s,
1,898,040 KiB peak RSS, zero swaps, exit 0). It uses the previously verified
next-word contract. It establishes an absorbing success transition and a
single rejecting/accepting transition over arbitrary owned states satisfying
the explicit next-word precondition; it does not assert a full caller law.

The new host workspace reuses this worker's continuation-7 compiler caches
through symlinks. It has its own sources, receipts, worker lock and snapshots.
No peer source or object is replaced. All host gates have MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64, four jobs and the required
four-thread linker flag. Input receipts carry exact source hashes in addition
to the base revision; additive source edits are committed with their receipts.

The scalar next-step certificate replaces the scalar-summary timeout;
`ProverCommitStepLoop.caller_step_induction` proves the extracted early-return
caller equals sixteen applications of the **newly extracted** `try_step`.
It handles arbitrary callbacks, successful absorbing states, rejection and
Aeneas fail/div. The new extraction contains concrete M31/CM31/QM31 addition;
no external-function template is adopted. Two intermediate extractions
retaining opaque addition are excluded. The Types-only port is the existing
explicit discriminant instance migration; its literal diff is retained.

`ProverCommitFourSteps.collect_extracted_steps` proves composition for every
number of scalar calls by induction; `qm31_collect` identifies the actual
extracted tower caller with four such calls, including left-to-right
coordinate order and the exact failure state. Kani independently executes
the actual shipped mask/source `qm31` bodies over an arbitrary shared
four-entry scalar-result/successor-state trace. Both pass. These stubs are
relational inputs, **not** unproved scalar summaries installed as contracts.
The trace allows arbitrary successors and success values; the error value is
the scalar callers' only actual error, `MaskSampleExhausted`. Callback count
and every state field agree on both success and early exit.

`ProverCommitFoldSteps.m31_fold/qm31_fold` lift the extracted row transitions
to every symbolic row list by induction, preserving monadic fail/div. The
single-row Kani checks execute the filter/fold operation with an arbitrary
accumulated sum, value, activity flag, row and dependent index. Both pass.
These prove the iteration algebra; they do not re-extract the previously
unsupported shipped `Enumerate`/`IterMut` outer loops or establish their
source-to-list transport.

| Target | Exit | Wall s | RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| mask four-coordinate trace | 0 | 5.962 | 611700 | 0 |
| source four-coordinate trace | 0 | 8.008 | 715164 | 0 |
| M31 balancing row | 0 | 3.600 | 490376 | 0 |
| QM31 balancing row | 0 | 3.786 | 490824 | 0 |
| final Charon / Aeneas extraction | 0 / 0 | 23.703 / 0.504 | 661108 / 80960 | 0 |

J8268/8269 compile
Types/Funs independently. J8270 scalar induction, J8271 row induction and
J8273 coordinate composition all exit 0, with 17 standard-axiom audits in
total and zero swaps. J8267 is an excluded attribute-port draft; J8272 is an
excluded elaboration draft. An early Rust draft fails to compile the
source seed's `Zeroizing` carrier; a second reaches a small `memcmp`
unwinding assertion. The replacements correct the carrier and set the
32-byte comparison's explicit unwinding bound to 34. No unwinding check is
disabled, no timeout or memory cap is increased.

## Stage 2: caller transport

`ProverCommitCallerObstruction.all_failure_not_law` is a checked
counterexample to deleting the caller premise for arbitrary endpoint inputs:
replacing only a seed prover's `tapeOf` by `none` contradicts `CallerLaw`.
The proof uses the existing nonvacuous `decoder_has_success` and the exact
input transport; no concrete stream or large finite carrier is reduced.
`failedCaller_not_law` supplies that explicit record update. J8277: exit 0,
wall 1.88 s, peak RSS 4,028,632 KiB, zero swaps, two standard-axiom audits.
J8274 is an excluded elaboration draft; J8275 is the accepted narrower
predecessor (1.80 s, 4,027,104 KiB, zero swaps).

This is a definition-level independence result, **not** a counterexample to
the shipped prover. It pinpoints why composing the verified scalar and tower
callees cannot complete the requested source law: no existing definition
identifies the inherited `seed.tapeOf` with the shipped outer raw-sample
producer. `source-frontier.json` verifies that all four outer/balancing
function bodies and both translation tools match the retained failing
aggregate-lowering evidence. No unchanged aggregate lowering is repeated.
The previous `Enumerate`/`IterMut` and Aeneas loop-boundary failures are not
certificates. A new owned reference, even with proved iteration, does not
supply that absent execution/carrier/order join.

The actual next obligations are (i) a valid shipped outer-loop lowering or
relational step-to-loop execution certificate, (ii) its raw pre-balance
sample projection and complete coordinate bijection, and (iii) its exact
connection to the endpoint seed's `tapeOf` on every pair of block answers.
`CallerLaw` remains a named premise, with no unverified contract or axiom
inserted to bridge these obligations.

## Stage 3: universal read coverage and endpoint

`ProverCommitReferenceReads.next_support` proves that the extracted next-word
operation depends only on its current domain/seed/LE64-counter frame.
`transition_support`, `scalar_support`, `all_calls_support`, and
`tower_support` lift this to every scalar transition, the actual extracted
sixteen-try caller, an arbitrary number of scalar calls, and the extracted
four-coordinate caller. Callbacks may fail or diverge; the theorem uses
agreement on expander frames and does not assume a globally equal oracle.
J8278: exit 0, wall 1.84 s, peak RSS 4,013,224 KiB, zero swaps; five
standard-axiom audits. J8276 is an excluded syntax draft.

This establishes a universal **reference expander support** result. It does
not identify actual commitment read logs, prove no counter reuse, construct
the outer producer's typed positions, or cover binary tree nodes/leaves,
attempt bindings, the three seeds and all per-leaf salts. Those are distinct
source execution obligations. The aggregate source obstruction recorded in
stage 2 also prevents claiming their universal runtime read completeness.

The new module `PrivacyR1FinalProtocolCallerScope` is built on the existing
`PrivacyR1FinalProtocolCaller`. `tapeOf_inherited` checks definitionally that
protocol construction preserves exactly the seed's decoder.
`caller_not_automatic` instantiates the all-failure counterexample at this
actual endpoint constructor. J8279: exit 0, wall 2.46 s, peak RSS 4,070,356
KiB, zero swaps, two new standard-axiom audits plus the unchanged endpoint
audit. The endpoint's experiment, simulator, error bound and signature are
unchanged. No complete shipped-source row or endpoint premise is discharged;
the requested deletion-only diff is therefore empty, rather than a weakened
statement. `checklist-deletion-audit.json` and `checklist-deletions.diff`
record that fact mechanically.

## Before (verbatim from continuation 7 after-table)

```text
| R_commit_D80.roots/nodes | AddressAt for all three roots/internal binary parents, child order, padded folded geometry, byte carrier and D81 grammar. Do not substitute eight-way C2 recovery for binary recovery. |
| R_commit_D80.leaves | Exact 0x71/0xf1/0x72 tags, packed leafVal/trailing salt, private-leaf backend and byte/digest conversions, on the actual prover tree. |
| R_commit_D80.bindings | Both secret-attempt binding reads, source/public/variant mapping, context encoding and digest answers (P`R1Z/LayoutR1PBin.lean:133`). |
| R_commit_D80.seeds | All three seed derivations, reserved secret distribution and source/D stream selection (P`R1Z/LayoutR1PBin.lean:136`). |
| R_commit_D80.salts | Full per-leaf secret salt derivation, nonce/tree/secret binding and LE32(u) (P`R1Z/LayoutR1PBin.lean:140`); verifier facts only consume disclosed salts. |
| R_commit_D80.mask_expander/source_expander | Stream/domain/seed/LE64(counter), eight words per block, no counter reuse, index/stream selection and complete hash-read coverage (P`R1Z/LayoutR1PBin.lean:131`). |
| R_commit_quotient_fibres, cF | Equal successful fibres on the H1 quotient; measure-preserving completion is proved. The explicit sequential wordsE decoder has a derived fibre constant and a successful input. The new endpoint derives this premise from one typed CallerLaw, including an output-coordinate equivalence; proving CallerLaw for the actual source remains open. |
| R_commit_exhaustion | Every tapeOf failure must imply one of the actual two 16-try little-endian stream-exhaustion events. Exact consuming wordsE-to-Exhausted classification is proved, and the endpoint derives this premise from CallerLaw. The shipped source-to-decoder caller/cursor equation remains open. |
| R_commit_counter₁/₂, R_commit_stream₁/₂, R_commit_cell_count, R_commit_blocks₁/₂ | All coordinate-model count, canonical stream/block and counter bounds are proved and derived in the endpoint from CallerLaw. The universal shipped caller/read-completeness instance remains open; model cardinalities do not establish source coverage. |
```

## After (verbatim; no complete shipped-source row removed)

```text
| R_commit_D80.roots/nodes | AddressAt for all three roots/internal binary parents, child order, padded folded geometry, byte carrier and D81 grammar. Do not substitute eight-way C2 recovery for binary recovery. |
| R_commit_D80.leaves | Exact 0x71/0xf1/0x72 tags, packed leafVal/trailing salt, private-leaf backend and byte/digest conversions, on the actual prover tree. |
| R_commit_D80.bindings | Both secret-attempt binding reads, source/public/variant mapping, context encoding and digest answers (P`R1Z/LayoutR1PBin.lean:133`). |
| R_commit_D80.seeds | All three seed derivations, reserved secret distribution and source/D stream selection (P`R1Z/LayoutR1PBin.lean:136`). |
| R_commit_D80.salts | Full per-leaf secret salt derivation, nonce/tree/secret binding and LE32(u) (P`R1Z/LayoutR1PBin.lean:140`); verifier facts only consume disclosed salts. |
| R_commit_D80.mask_expander/source_expander | Stream/domain/seed/LE64(counter), eight words per block, no counter reuse, index/stream selection and complete hash-read coverage (P`R1Z/LayoutR1PBin.lean:131`). |
| R_commit_quotient_fibres, cF | Equal successful fibres on the H1 quotient; measure-preserving completion is proved. The explicit sequential wordsE decoder has a derived fibre constant and a successful input. The new endpoint derives this premise from one typed CallerLaw, including an output-coordinate equivalence; proving CallerLaw for the actual source remains open. |
| R_commit_exhaustion | Every tapeOf failure must imply one of the actual two 16-try little-endian stream-exhaustion events. Exact consuming wordsE-to-Exhausted classification is proved, and the endpoint derives this premise from CallerLaw. The shipped source-to-decoder caller/cursor equation remains open. |
| R_commit_counter₁/₂, R_commit_stream₁/₂, R_commit_cell_count, R_commit_blocks₁/₂ | All coordinate-model count, canonical stream/block and counter bounds are proved and derived in the endpoint from CallerLaw. The universal shipped caller/read-completeness instance remains open; model cardinalities do not establish source coverage. |
```

## Further balancing-lowering attempt and demonstrated stopping point

After the first coherent new-cone audit was green, a **new, narrower**
extraction targeted just the owned `balance_m31_owned` and
`balance_qm31_owned` functions, with concrete field arithmetic. This was not
a rerun of either timed-out CBMC comparison or the old shipped builder
extraction. Charon exits 0, `has_errors=false`, wall 23.917 s, peak RSS
668,336 KiB, zero swaps. Aeneas exits **2**, wall 0.327 s, peak RSS
67,936 KiB, zero swaps: `Not_found` in
`InterpReduceCollapse.collapse_ctx_following_sequence` (line 1991), called
from `InterpJoin.match_ctx_with_target` and `InterpLoops` at the loop
boundary. Full stdout/stderr, tool/source pins, exact command and LLBC
hash/size are retained in `balance-*-v1` receipts and
`extraction/excluded-balance-artifact.json`. No output is adopted as a
certificate, no axiom replaces the failed lowering, and it is not replayed.

Thus even this owned whole-loop-to-fold transport remains a demonstrated
translator obstruction, distinct from the now-small verified row
comparison and its Lean iteration algebra. The full shipped material-loop
join, raw coordinate projection/order and seed `tapeOf` identification are
still required for CallerLaw. The trees/bindings/seeds/salts and complete
source callback-log coverage remain independent. No complete source row is
closed, and no endpoint premise is removed.

## Final coherent audit and frozen artifacts

`R1Z.ProverCommit8Audit`, J**8280**, imports the previous complete prover
cone and every new theorem module. Exit **0**, wall **2.31 s**, peak RSS
**4,032,952 KiB**, **zero swaps**. All **27** printed audits contain only
`propext`, `Classical.choice`, `Quot.sound`, a subset, or no axioms. Source
revision **`7665aa666`** contains every adopted theorem and Rust source;
the additive audit file is pinned by its exact SHA-256, literal attempted
source and dependency fingerprint. The subsequent balancing experiment
changes only evidence and extraction configuration, so this unchanged
coherent audit is not rerun. Assigned attempts consumed through **8280**;
next available **8281**. Shared-module replacements are limited to this
branch's newly created namespace/modules; all privacy-worker modules are
untouched.

The single final ELF comparison after the last Rust source edit succeeds:

| Artifact | SHA-256 | Size bytes | Wall s | RSS KiB |
| --- | --- | ---: | ---: | ---: |
| default | dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34 | 1507400 | 2.284 | 203356 |
| devnet | fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78 | 1507400 | 2.234 | 202908 |
| pool | 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 | 605704 | 0.392 | 99580 |

All three builds and `cmp` calls exit 0 with zero swaps. Their exact frozen
features, toolchain, sources, cgroup reservations, compiler/linker flags and
commands are recorded in `frozen-elf-final-check.json` and receipts. No ELF,
LLBC, executable, `.olean`, archive or wallet key is committed. Keys and
build caches are retained on the host. No push, merge, deployment, key
cleanup, or peer-file edit was performed.

`harness/validate.py` checks all fourteen attempted Lean source identities,
ten accepted attempts, all 27 final audit lines, five accepted Kani targets,
896 Rust source identities, the empty deletion diff, all three byte-identical
ELFs, and the exact generated Funs identity. Earlier/excluded Rust source
configurations are reconstructed and hash-checked by `harness/source-map.py`;
all resource/error receipts remain verbatim. These are evidence validations,
not repeated compilation or regression runs. Raw generator/compiler output
retains upstream whitespace; adopted handwritten sources have no whitespace
errors.
