# R17 determinant sampler/source boundary

## Exact ideal bounded-rejection law — 2026-09-21

Base `82bc407b1cedf4cfb0346e83ba57c670fe820c4d` plus this changeset.
`AspisV8R17/BoundedRejection.lean` now compiles eight audited theorems.
For a finite alphabet D and n independent uniform tape entries, the sampler
returns the first accepted entry, or an explicit none on exhaustion. An
acceptance-preserving permutation transports output fibers bijectively;
swapping two accepted symbols proves equal output counts and probabilities.
The failure fiber is equivalent to n-tuples of rejected symbols, so its
probability is exactly `(#rejected)^n / (#D)^n`. Zero attempts are included.
This proves a finite ideal law, not independence of actual oracle answers,
nor a full QM31/circle sampler, adaptive-selection, or publication theorem.

Focused command: retained lake environment in `/Users/dominic/ZK/AspisFormal`,
`/usr/bin/time -l`, retained r17/r16 LEAN_PATH, `lean -j1 -M1800 -R SOURCE_ROOT
-o target/r17-lean/AspisV8R17/BoundedRejection.olean
SOURCE_ROOT/AspisV8R17/BoundedRejection.lean` (output path absolute in invocation).

| Target/attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| FiniteGames prerequisite object (missing cache) | 0 | 8.31 | 1297367040 | 0 |
| BoundedRejection initial | 1 | 1.94 | 1330102272 | 0 |
| BoundedRejection map fix / cardinal instance mismatch | 1 | 8.34 | 1330413568 | 0 |
| BoundedRejection six counting theorems | 0 | 4.64 | 1475051520 | 0 |
| BoundedRejection final eight theorems | 0 | 4.11 | 1476018176 | 0 |

The fixes use explicit list-map transport and instance-independent Nat.card
equalities, not stronger premises. Failed-attempt sorryAx audits are rejected.
Final eight `#print axioms` results contain only propext, Quot.sound, and
(for counting/probability) Classical.choice. No production changes or
unchanged full-suite replays occurred.

Next source-specific obligation remains the joint law of the actual bounded
multiword sampler under shared-oracle first assignments and adaptive transcript
selection, including public prequeries, distinct-point retries, intervening
absorbs, and visible aborts. The ideal law does not discharge that premise.

## Compiled first-assignment provenance — 2026-09-21

Base `3d5b2ae5cd9a75a4c781aecbd674016a3046079a` plus this changeset.
`AspisV8R17/FirstAssignment.lean` imports the retained R9 memoized expansion
and uses the exact retained `queryStep`, `Table` and cache laws. It does not
replace them with a fresh-output-per-call model.

The new interpreter records first assignments only when an address was
absent. Separate returned-answer and final-table projections prove:

* every returned answer persists in the final table;
* every final cached answer originates in the initial table or in a recorded
  first assignment;
* from an empty table, every final answer has a recorded assignment;
* selecting a bad returned/cached answer implies either an initially cached
  bad answer or a bad recorded first assignment;
* the number of recorded assignments is at most the number of calls;
* a public prequery followed by the same sampler query records exactly one
  assignment, ignoring the second call's unused fresh-tape value.

All ten theorems compile. They hold pathwise for every realized call list,
including lists produced adaptively. This does not assert a distribution
on adaptive lists, nor that their fresh-tape components are independent.
The initial-table alternative is explicit: prequeries are not discarded.
An execution starting from an empty table must include external queries,
commitment/seed-expansion queries and other shared-oracle calls in its
provenance, not only sampler calls. Paired reservation/installation events
also need correspondence to their earlier assignments when composing this
fragment with the full eager/delayed operational machine.

### Precise remaining probability premise

The provenance theorem supports a union-bound route, but does not supply
per-assignment probabilities. To use such a bound, the bad-answer predicate
or candidate test must be justified relative to the information available
before that answer's first assignment, with any later transcript selection
explicitly accounted for. An arbitrary predicate chosen after seeing the
answer can mark every observed answer bad; provenance alone cannot make
that event rare. The actual determinant depends jointly on u,v,alpha and
on bounded multiword sampler paths, so a static single-answer predicate is
not yet a source instantiation. Establish the joint sampler/selection law
at first assignments, preserving the distinct-point loop and visible aborts.
No numerical source loss, full simulator or privacy/soundness result follows
from these deterministic lemmas.

### Focused Lean evidence

Commands ran in `/Users/dominic/ZK/AspisFormal` via `/usr/bin/time -l`,
the retained lake environment/LEAN_PATH wrapper and `lean -j1 -M1800`.
The three unchanged prerequisites lacked cached objects in this workspace;
they were emitted with `-R SOURCE_ROOT -o CACHED_TARGET.olean` before the
new leaf. SOURCE_ROOT is the privacy worktree's
`docs/research/v8-full-view-zk-20260912/lean`. No full replay occurred.

| Exact target/attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| AspisV8PairedCommitment/Table.lean object | 0 | 5.68 | 868925440 | 0 |
| AspisV8PairedCommitment/ShadowTable.lean object | 0 | 1.20 | 867729408 | 0 |
| AspisV8R9/MemoizedExpansion.lean object | 0 | 1.18 | 858275840 | 0 |
| AspisV8R17/FirstAssignment.lean initial | 1 | 1.31 | 863141888 | 0 |
| FirstAssignment.lean corrected six-theorem fragment | 0 | 2.67 | 861880320 | 0 |
| FirstAssignment.lean final returned-answer bridge | 0 | 2.89 | 864550912 | 0 |

The first attempt needed the already-rewritten none=none proof and an
explicit Nat.le_refl; its sorryAx audits are rejected. Final audits use
propext only, except the length theorem also uses Quot.sound. Prerequisite
audits use propext or no axioms. Exact output is in the command-tool record.
Only an unnecessary-simpa warning remains in the new leaf. No Rust/source
sampler change or unchanged runtime suite was run.

Date: 2026-09-21. Base `48a2cd311687e1d1c836ecb7b876f3a351fc00a8`
plus this changeset. This is an operational premise audit, not a new attack
on SHA-256, a source probability theorem, or a privacy/soundness verdict.

## Source pins inspected

The retained stage is `/tmp/aspis-r15-host.drHYn9/r17-two-channel-source-v19`.
The current core transcript and circle files are byte-identical to that
stage, checked with SHA-256, not inferred from their names.

| File | SHA-256 |
| --- | --- |
| `crates/aspis-core/src/transcript.rs` (worktree and stage) | `be036d144b9fe0c8119d9f6fdd8ca2167d1379f7d1d785fa2f197200b9f7d119` |
| `crates/aspis-core/src/circle.rs` (worktree and stage) | `8f6f0f32c8dd93e3ee459df0c1d0ef710b01996d3bc929dbeffb3f7d14a0227c` |
| staged `docs/research/v8-no-work-100-20260907/experiments/inactive_row_binding.rs` | `53d2bba4bb1320fb8272b061243045ffeac2bd1f5944127413e1bff560a6411f` |
| staged `.../experiments/relation_callback.rs` | `22c0837ec4f14a0b9a3795b6bdc40144911468c5499836eca48cc503ce698b9e` |
| `tools/r17_host_relation.rs` | `7464ff262cf5f7472b496f30b33f9e9a4772de88bc2b7dc45490cab4e49f9fda` |
| `tools/stage_r17_two_channel_host.py` | `e915651d72cf64eac073c2b2529ab818cda1821d27b764cfd5f97247e3192428` |

## Exact operational order and bounded loops

`Transcript::squeeze_block` hashes `state || 0x01` for the output and
`state || 0x02` for the next state. Each QM31 draw starts a new block,
takes four canonical M31 limbs, and discards any unconsumed words on
return. Each limb gets at most eight attempts; a word's high bit is masked
and the single value P is rejected. At most 32 words/four squeeze blocks
are consumed per QM31 call. Exhaustion returns an error, never a fallback.

`challenge_secure_circle_point` makes at most three QM31 calls. It rejects
singular rational parameters and parameters in CM31, preserving the
distinction between inner limb exhaustion and outer parameter exhaustion.

The actual R17 `to_gamma` wrapper adds another bounded loop:

1. Absorb all point claims, then draw the first secure circle point.
2. Absorb that point's 29 component values.
3. Try at most three secure-circle draws for a point unequal to the first.
   Any sampler error propagates immediately; equality alone causes retry.
4. Absorb the second component vector and batch nonce; draw nonzero gamma.
5. `prepare` absorbs the inactive claim, draws nonzero kappa, constructs
   both opening channels, absorbs descriptor/weights/claim and draws tau.
6. Absorb the first relation polynomial and fold nonce; draw ordinary QM31
   alpha, then absorb the final arrays before query selection.

Thus u,v,alpha are not three adjacent calls. For these three parameters
alone, the loops allow at most 3+9+1=13 QM31 calls, hence at most 52 squeeze
blocks/104 squeeze-and-advance hash calls. This excludes all intervening
gamma/kappa/tau, absorbs, commitments, seed expansion, other protocol
challenges and external oracle calls. It is a source control-flow upper
bound, not a probability loss or a bound on the full oracle transcript.

## Two distinct freshness pitfalls

Advancing state does not logically guarantee distinct future hash inputs
for an arbitrary injected HashFn: a cycling deterministic backend repeats
the same squeeze address and the same accepted challenges. This is a
negative control for a universal operational premise, not evidence that
the selected SHA-256 backend has such cycles.

More importantly, even with the actual SHA-256 backend, a publicly known
next squeeze input can be queried before the sampler requests it. The new
test demonstrates this at the known initial state using the identical
33-byte input, not two different inputs with a collision. Therefore the
event “the sampler's address is already in the oracle table” cannot simply
be charged as a negligible collision/secret-preimage event. This observation
does not establish biased challenges or a protocol attack: the cached
answer may have been uniform when first assigned. It does establish that
conditioning on an already queried answer and claiming it is still a fresh
independent draw is invalid.

## Required next proposition

Use the retained R9 memoized expansion/operational trace machinery to
identify first assignments of the relevant oracle entries, including
external prequeries. Bound the determinant-zero event under that joint
execution, with explicit query and transcript-selection budgets; charge
actual state/input collisions separately. Public cached answers must be
reused, not resampled or automatically charged as secret first-hit events.

For a genuinely fresh independent-word ideal sampler, the intended accepted
parameter sets are S=QM31 minus CM31 for u, S minus {u} for v, and QM31 for
alpha. Rational-map injectivity explains the distinctness restriction.
Turning this into a law of the actual shared-oracle execution requires
the first-assignment and selection argument above, plus the bounded
sampler refinement and visible-failure accounting. Conditioning on final
publication cannot be silently substituted for conditioning on local
sampler success. No numerical source loss is established here.

The existing `AspisV8R15/ExactTowerBase.lean` retains the exact M31/CM31/QM31
tower and its nonsquare certificate; reuse it for coefficient embedding,
not a new field construction. Its Rust-word refinement is a separate gate.
The compiled nonzero determinant polynomial is unchanged. Joint residual
coverage, commitment/seed hops, a full simulator and soundness remain open.

## Focused executable evidence

New target: `crates/aspis-core/tests/r17_transcript_freshness.rs`, using the
actual core Transcript and circle APIs. Five tests pass:

* cycling advance does not universally imply fresh inputs;
* a real SHA-256 public squeeze can be prequeried without a collision;
* maximal successful limb retries consume exactly four blocks;
* inner and outer sampler exhaustion errors remain distinct;
* the core circle sampler alone does not enforce distinct consecutive points.

Command: `cargo test --offline --locked --release --jobs 1 -p aspis-core
--test r17_transcript_freshness -- --nocapture`, in the isolated worktree.
No dense arithmetic or proof generation is performed; time is in compiling
the small new integration target. The initial four-test run passed, exit 0,
1.69s, peak RSS 137641984 bytes, swaps 0. Its attempted macOS RLIMIT_DATA
setup failed before the command; it must not be represented as a capped run.
A separate RLIMIT_AS setup preflight also failed, without launching a job.

After adding the SHA-256 prequery test, the final run used a process-group
watchdog that samples aggregate descendant RSS every 50ms and terminates
above 524288 KiB. Exit 0, five passed, wall 1.85s, `/usr/bin/time -l` peak
RSS 141672448 bytes, swaps 0; watchdog sampled aggregate peak 235408 KiB.
This is a sampled guard, not a kernel cgroup cap. No large job was run.
Existing cfg/dead-code warnings remain. Exact output is in the tool record.
No Lean changed or new Lean result is claimed; no unchanged full suite,
production path, wallet, deployment or existing negative regression changed.
