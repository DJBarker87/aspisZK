# Prover commitment source facts — 2026-10-20

Branch `codex/cx-prover-commit2-20261020`, continuing `f2a598c6a`.
Retained Rust changes are at `29d198eed` (salt loop) and `1fc9133aa`
(expander helpers); the checked proof/adapter source revision is `87fdbd024`. No verifier source or parked freeze was changed.
`verifier.rs` is byte-identical to adopted freeze `b2727acd3`, SHA256
`8c872d42bdaa245cc540be6b26d17108a5cb40754b8befb79e147f5843b1f756`.

The initial salt-loop blocker is repaired under the lead's prover-refactor
gate. **Full source closure remains blocked. No complete checklist row in
PRIVACY-FINAL-20261020.md is discharged.** This packet supplies 26 checked
subsidiary theorems, qualified prover refactors, and precise builder/reference
blockers. It does not construct a Rust `R1ProverP`, a reserved-secret law,
or an unconditional privacy theorem. No equal-fibre, causal or ordered-log
source law is asserted.

Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit2-20261020/`.
The original stopped packet remains under `evidence/prover-commit-20261020/`;
its former report is available with `git show f2a598c6a:docs/research/v8-r0-zk-20261009/r1p-final/PROVER-COMMIT-20261020.md`.

## Checked facts and exact remaining joins

`P` below means `docs/research/v8-r0-zk-20261009/lean/R1Z/`.
The actual D80 target is P`PremisesR1PBin.lean:19` (`AddressAt`), decomposed
at `:29` (`commit_bytes_iff`). These quantify over all secrets, tapes,
challenges and arbitrary answer vectors. The new grammar joins retain those
byte-grammar parameters, but require explicit source-carrier images; they do
not supply an arbitrary `Pr.caddr` equation by naming it a source instance.

| Checklist item | Checked result against actual definitions | Still open |
|---|---|---|
| `R_commit_D80.salts` | P`ProverCommitSaltSource.lean:23` proves the extracted method's six callback slices, conditional on successful context validation and attempt binding. P`ProverCommitSaltBytes.lean:17,103` proves LE32 and the domain/binding/nonce/tag/index/secret concatenation. P`ProverCommitGrammarSource.lean:15` joins it to P`LayoutR1PBin.lean:140` with explicit binding, nonce, secret, tag and index images. Actual Rust: `crates/aspis-prover/src/state_only_entropy.rs:568`. | Complete caller/loop coverage, successful context/binding correspondence, byte images and the total counterfactual `Pr.caddr` instance. |
| `R_commit_D80.seeds` | P`ProverCommitStreamSource.lean:30` proves the mask-seed callback slices, conditional on the actual nonzero comparison and context encoding. P`ProverCommitStreamBytes.lean:28` checks its domain. Actual Rust: `crates/aspis-prover/src/state_only_hiding.rs:387`. | Source-seed and D-seed derivations (`state_only_entropy.rs:426,650`), encoding/caller joins, source/D stream selection, OS/conditioning/reservation law. No reserved-secret distribution is asserted. |
| `mask_expander / source_expander` | P`ProverCommitStreamSource.lean:14,19` proves both extracted refill helpers' callback slices. P`ProverCommitSaltBytes.lean:49` proves LE64. P`ProverCommitStreamBytes.lean:12,18,23` checks concatenation and both exact domains; P`ProverCommitGrammarSource.lean:30,43` joins these to P`LayoutR1PBin.lean:131` given seed-slot/counter images. | Initial-state, index/stream selection, all eight successive reads, invocation bounds, global non-reuse and complete source-read coverage. |
| Eight words / counters | P`ProverCommitStreamBytes.lean:36` proves the actual wrapping-add operation increments normally when `counter.val+1<2^64`. Its `:45,47` gives the `Fin 8 × Fin 4 ≃ Fin 32` partition and source offset `4*word+limb`. | This is a bounded machine-step and byte-partition fact, not the universal execution invariant or a proof that an unbounded wrapping stream never repeats. |
| `R_commit_D80.leaves` | P`ProverCommitLeafSource.lean:24,36,44` proves the generic `private_leaf_hash` callback and its D81 grammar at explicit tag choices 0x71/0xf1/0x72, including trailing salt. P`ProverCommitGrammarSource.lean:56` joins to P`LayoutR1PBin.lean:142` with explicit value/salt images. Actual Rust: `crates/aspis-core/src/state_only_private_merkle.rs:29,40`. | Actual tree caller and exact packed `Pr.leafVal`: `host_commitment.rs:152,188,199`, `prover.rs:229`. Generic grammar does not identify those values. |
| `R_commit_exhaustion` | P`ProverCommitExhaustionScope.lean:38,46` gives a symbolic, capacity-respecting counterexample to using padded-budget exhaustion as an iff for a shorter decode. | Actual source `tapeOf`, `wordsE`, failure classification and the one-way P`FinalR1PBin.lean:54` premise remain uninstantiated. An iff at the exact actual consumption count is not refuted or proved here. |
| `R_commit_counter₁/₂`, `stream₁/₂`, `cell_count`, `blocks₁/₂` | Only the bounded counter step and eight-word arithmetic above are added. | Universal source counts/coverage and transport to P`CommitReadsR1.lean:210,289` and the final source premises. Existing fixture budgets are not this proof. |

The grammar joins keep the carrier images as named hypotheses. Neither they
nor successful fixture tests construct the full `R1ProverP` or discharge
`AddressAt`. P`PrivacyR1Final.privacy_R1_final` remains its existing conditional
endpoint; no source coupling is supplied by this job.

## Retained refactors and behaviour gate

The salt loop carries its `Result` through the loop and uses an owned-vector
step. After an error it performs no further derivation calls and returns that
error. The two refill hash calls use small helpers; the source expander copies
its hash pointer, seed and counter before assigning its block. Sampling order,
domains, encodings and retry limits are unchanged. The larger builder
experiments and the reference are **not** retained production changes.

Both retained stages pass the lead's gate on the adopted compact S2 format:

| Gate | Salt stage | Expander stage |
|---|---|---|
| Before/after deterministic masked fixtures | Transfer and withdrawal: byte-identical, 57,607 bytes each; strict tx1+tx2 and dense acceptance | Both remain byte-identical to the original baseline; strict and dense acceptance |
| P_R1 gate | 8/8 accepted and verified; separate retrying invocation accepted in one attempt | 8/8 accepted and verified; separate retrying invocation accepted in one attempt |
| Library / D78 tests | 33 passed, 0 failed, 0 ignored, including all four simulator tests | 33 passed, 0 failed, 0 ignored, including all four simulator tests |

Proof hashes are `eaaf4bfff6c5ee992f41f031bea02c46f48b6ace64cc716196a3d1d5f92400a2`
(transfer) and `fc5499f1ae7fc6e2763e4bc174dfa3315cc79917d4be78dd4d9fa5b8f66cc286`
(withdrawal). These are the two supported adopted-format fixture cases;
retired S1/eight-way proofs were not regenerated.

The salt stage also ran the four-seed D78 timing gate: every proof passed
strict and dense under its programmed oracle, every programmed address was
read, and both real-hash checks rejected. This is runtime evidence, not a
Rust simulator coupling or a distribution theorem.

## Exact blocker frontier

The salt, leaf and both expander LLBC artifacts have `has_errors=false` and
Aeneas exits 0. The final salt extraction was repeated after the expander
source change to pin the retained source: generated Types are byte-identical;
Funs differs only in the binding function's source-line comment (854→853).
`final-salts-code-identity.json` and the one-line patch check that all other
text is identical. The already checked definitions are reused.

The larger builder cone is not a clean extraction. Charon returns 0 but sets
`has_errors=true`, with mismatched iterator clauses involving `Enumerate`
and `IterMut`; those artifacts are not accepted lowering certificates.
The original builder then fails Aeneas at `state_only_hiding.rs:461` in
`InterpAbs.ml:191`. Isolated carried-result C1/G/H1 forms advance the
translator to the D loop. A carried D form still raises an internal error at
`state_only_entropy.rs:656`, `InterpMatchCtxs.ml:2715`. No such builder change
was installed in the shipped source or qualified by the runtime gates.

A test/extraction-only reference replaces iterator balancing with explicit
loops. Its LLBC is clean (`has_errors=false`), but pinned Aeneas exits 2 with
`Not_found`, `InterpReduceCollapse.ml:1991`, while collapsing loop contexts.
Its source, recipe, LLBC hash and complete logs are retained. It is not a
translating reference and no reference Lean module is imported.

The preparatory Kani harness compares the shipped and reference mask builder
at 3,803 cells and 1,024 rows. Kani 0.67.0 exits 1 during compilation:

```
error[E0277]: the trait bound
for<'a, 'b> fn(&'a [&'b [u8]]) -> [u8; 32]: kani::Arbitrary
is not satisfied
```

This harness has no model of admitted byte-oracle callbacks; native function
pointers are not the desired universal byte-oracle interface. No fixed-backend
or callback-trace equivalence was proved, no solver equality result exists,
and this diagnostic does not refute source equivalence. The clean reference's
Aeneas failure and the missing Kani callback bridge remain blockers. No
substitute hash was used to claim an all-input certificate.

One builder experiment initially selected the original manifest instead of
the isolated one; its receipts are explicitly excluded as refactor evidence.
Kani's first invocation passed an empty RUSTFLAGS argument and failed before
source compilation; v2 removes that environment error and exposes E0277.
These are recorded harness failures, not proof or resource failures.

## Exhaustion scope and count correction

The requested iff must not use the padded worst-case count as if it were
actual consumption. P`FinalR1PBin.lean:54` defines only the forward implication.
The checked P`ProverCommitExhaustionScope.lean:46` constructs
`ws : Fin (90112*8) → Word` for which

```
limbPos ws 21375 = some 21375
Exhausted ws 45056
```

The prefix words are accepted zeros; a later unused 16-word window contains
`0x7fffffff`. The carrier satisfies the full `16*45056 = 8*90112` budget.
The proof first establishes generic prefix/window lemmas and applies them;
it does not reduce a 45,056-step recurrence or enumerate the word space.
This refutes the padded-budget converse for a shorter decode, not an iff at
the exact source count or an arbitrary unconstructed Rust `tapeOf`.

The first-run report's `26*1024 + 10*1024 + 4*1024 + 4*1024` arithmetic is a
conservative model envelope, not an exact source sampling count. The source
**declares** 3,803 free cells and 214 copy-active rows
(`crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs:49,48`), and samples
H1 only on inactive nondependent rows (`state_only_hiding.rs:467`). If those
source length/count refinements are supplied, the limb arithmetic is
`3803 + 10*1024 + 4*1024 + 4*(1024-214-1) = 21375`; D uses 4,096.
Those declarations/readings are not new universal source-count theorems.
The upper envelope L1≤45,056, L2=4,096 remains conservative.

## Coherent verification and library boundary

All new Lean sources are additive to the privacy tree. The final
`R1Z.ProverCommitSourceAudit` imports the grammar joins, capacity-respecting
counterexample and unchanged `R1Z.PrivacyR1Final`. Env J attempt **8143** exits
0 in **1.90 s**, peak **4,015,932 KiB**, **0 swaps**. Its 27 complete axiom lines
cover all 26 new theorems plus `privacy_R1_final`; every set is exactly a
subset of `[propext, Classical.choice, Quot.sound]`.

| Final focused target | Attempt | Exit | Wall | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|---:|
| `ProverCommitSaltSource` | 8108 | 0 | 1.68 s | 2,553,472 | 0 |
| `ProverCommitLeafSource` | 8112 | 0 | 2.46 s | 4,012,224 | 0 |
| `ProverCommitSaltBytes` (LE32/LE64/salt bytes) | 8130 | 0 | 3.58 s | 4,020,336 | 0 |
| `ProverCommitStreamSource` after scoped-instance rebuild | 8138 | 0 | 1.46 s | 2,563,708 | 0 |
| `ProverCommitStreamBytes` | 8140 | 0 | 2.19 s | 4,015,192 | 0 |
| `ProverCommitGrammarSource` | 8132 | 0 | 2.10 s | 4,010,888 | 0 |
| `ProverCommitExhaustionScope` (full capacity) | 8142 | 0 | 1.57 s | 2,385,904 | 0 |
| `ProverCommitSourceAudit` | 8143 | 0 | 1.90 s | 4,015,932 | 0 |

The generated discriminant attribute produced the same global instance name
in two otherwise namespaced cones. The expander Types now uses its explicit
0–4 definition with a scoped instance; constructors and discriminant values
are unchanged. `scope-discriminants.py` records that expansion. Only this
job's own new shared sources/objects were replaced, with prior versions
snapshotted under the branch's host workspace; no pre-existing project
module was overwritten.

Rebuilding that type left some parent `.olean` hashes unchanged. Because direct
import hashes stayed unchanged, two attempted launches were refused. The
transitive environment had changed. The final driver records
all own-cone transitive object hashes, including the changed Types, and uses
those new inputs for the dependent checks. No launcher/global lock was
modified or bypassed. Refused/preflight-only attempt numbers have no compiler
or time receipt and are distinguished from actual Lean executions.

External adapters define the live `Zeroizing` payload, AsRef/Deref, Result
mapping and the two numeric constants. The P6 differential harness checks
65,792 byte-array payload cases, two Result::map cases and both constants
against pinned Rust/zeroize 1.8.1; `library-model-check-v2` passes in 11.502 s,
peak 581,404 KiB, no swap. These are explicit library model choices for P6
review, not an OS entropy law or a new trust acceptance. Allocation/drop
operations are deliberately unsupported (`fail .panic`); no theorem here
claims their semantics or the successful totality of the whole salt wrapper.

The source base is `f2a598c6a` with each attempt's exact source SHA and import
fingerprint; accepted published-source content is additionally tied to the
code revision in `source-release.json`. `source-inventory.json`,
`accepted.json`, `attempts.jsonl`, full stdout/time logs, source/tool pins,
LLBC `has_errors` flags, binary/object hashes and source-span identity checks
are committed alongside the report. `collect.py` validates these without
launching Lean or Rust. Failed proof drafts' recovery `sorryAx` lines are
not accepted evidence.

All compiles used the existing `run-joint.sh`, env J, Lean 4.32.0,
`-j1 -M7000 -DElab.async=false`. Early focused scopes used 7 GiB, later
focused scopes 4 GiB, final audit scopes 6 GiB; all stayed at or below the
existing 7 GiB maximum. Extraction and Rust jobs used explicit capped scopes and no swap. Runtime
gates and Charon used optimized release builds and four Cargo jobs; Kani
stopped during compilation before symbolic unrolling or arithmetic execution. Full populated-cap
checks preceded launches; holds and live reductions of this job's caps are
recorded. No memory-killed job or unchanged larger-cap retry occurred.

No local Lean, full frozen-manifest replay, SBF rebuild, deployment, push,
wallet/account operation or key cleanup was performed. The exact remaining
work is the valid builder/reference translation and callback-equivalence
bridge, followed by actual caller/carrier/seed/tape/count/read-completeness
instances listed above. The final conditional privacy and soundness endpoints
remain conditional.
