# R17 determinant sampler/source boundary

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
