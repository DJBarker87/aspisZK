# R17 determinant sampler/source boundary

## Literal transcript/commitment address boundary — 2026-09-21

Base `856f3b90f28878c963c75e3c6f0da5f4499420b0` plus this changeset.
Inspected transcript.rs DOM constants and absorb/absorb_two/squeeze_block,
the actual V7 Merkle wrappers and private-leaf helper, and the retained v19
relation_callback.rs hash backend. The backend hashes concatenated slices;
slice boundaries are not additional address tags. Absorb framing is
`state32 || 0 || label || data`, squeeze `state32 || 1`, advance `state32 || 2`.
Private leaves start `16 || tree_tag || value || salt32`; parents start 17
and have two 26-byte child digests. Merkle truncation affects returned digests,
not the byte-address identity in the complete 256-bit shared oracle.

`AspisV8R17/TranscriptAddresses.lean` reuses the retained Domains definitions
and compiles seven proofs: squeeze/advance lengths 33; distinct squeeze and
advance inputs even across arbitrary states; a length-33 address is neither
a salted private leaf nor a fixed-width V7 parent; absorb_two concatenation;
and explicit absorb/leaf grammar overlap. The overlap has a 32-byte state,
32-byte salt and leaf value length 32+payload.length. It is a grammar witness,
not a valid-witness/protocol-state reachability proof or SHA attack.

Consequence: do not partition ALL transcript addresses from leaf addresses
using tags alone. State is before the transcript domain, whereas the leaf
tag is first. Squeeze/advance are separated from these commitment families
by length; absorbs require actual shared-address/first-hit accounting. The
existing R9 ascii-expander/leaf separation remains valid for its inspected
families, but does not establish disjointness from state-prefixed absorbs.
Adversarial oracle calls remain arbitrary byte addresses.

This is source-checked framing algebra, not automatic Rust extraction. The
first combined-execution obligation remains to bind every source/adversary
call to the common byte log and justify its adaptive event bound, including
absorb/leaf intersections and salt exposure. No independent-oracle or new
hiding assumption has been introduced; production paths are unchanged.

Checked source pins (core paths under crates/aspis-core/src):

| File | SHA-256 |
| --- | --- |
| transcript.rs | be036d144b9fe0c8119d9f6fdd8ca2167d1379f7d1d785fa2f197200b9f7d119 |
| v7_merkle208.rs, current and v19 identical | 071ade1236140fdae559bb7b607ac9b7ee299e74eccb16b3385e3b1bbf215fdf |
| state_only_private_merkle.rs | f0edc31d07d30f5b19fcaf872fba18678d13d1ba5fac1199f1f4d2be74c74f9b |
| v19 experiments/relation_callback.rs | 22c0837ec4f14a0b9a3795b6bdc40144911468c5499836eca48cc503ce698b9e |

Focused cached lake command uses -j1 -M1800 and matching objects:

| Target/attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| TranscriptAddresses, Domains object missing | 1 | 3.71 | 668811264 | 0 |
| AspisV8PairedCommitment/Domains prerequisite object | 0 | 4.19 | 1196670976 | 0 |
| AspisV8R17/TranscriptAddresses final seven proofs | 0 | 1.54 | 1201946624 | 0 |

Seven #print axioms audits use propext, with Quot.sound on the length
contradictions and overlap; no sorryAx or additional axioms. One unused-simp
warning remains. Domains was emitted only because its required object was
absent. No runtime or full-manifest replay occurred.

## Adaptive law connected to retained memoization — 2026-09-21

Base `c6dc9be83c5ee128e509d9480ec8277823dba273` plus this changeset.
`AspisV8R17/AdaptiveMemoized.lean` imports both AdaptiveOracle and the
retained FirstAssignment/R9 cache chain. It does not define a replacement
queryStep. A compatible cache stores only answers from the same complete H.
Each query returns H(i), including cache hits, and preserves compatibility.
The adaptive memoRun interpreter using queryStep has exactly the same full
address/answer trace as AdaptiveOracle.run, for any compatible starting table.

The cache-domain theorem is stronger than compatibility: for any realized
call list, the final table misses i iff the initial table misses i and no
call has address i. From an empty cache this equates a genuine miss with the
unread predicate in the deferred-decisions law. The final theorem establishes
equal joint masses (memoized prior trace=tr, next answer=a) for all a when
replaying tr leaves the next address absent. Public prequeries remain in tr;
repeated addresses cannot satisfy this miss premise. No independent fresh
value is asserted on a hit. The distribution is over complete uniform H,
not a postulated per-call independent tape.

Seven audited theorems compile. Five use propext alone; cache_missing_iff
also uses Quot.sound; memoized_fresh_joint_probabilities additionally uses
Classical.choice. No sorryAx, new cryptographic assumption or source mutation.

Still required: connect the actual combined source/adversary log and its
byte-address encoding to this causal interpreter, including expansion and
commitment queries. Paired reservation/installation events require their
own operational correspondence; the cache bridge is for ordinary queryStep.
The multiword sampler and adaptive selection of joint determinant inputs
still need explicit first-assignment/loss accounting. Full privacy, simulator
construction, publication behavior and repair soundness are not concluded.

Focused cached lake command uses -j1 -M1800 and matching objects:

| Target/attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| AdaptiveMemoized, prerequisite object absent | 1 | 4.54 | 669532160 | 0 |
| FirstAssignment prerequisite object emission | 0 | 2.36 | 875233280 | 0 |
| AdaptiveMemoized final seven theorems | 0 | 4.44 | 1474527232 | 0 |

FirstAssignment was recompiled only because its required object was missing,
not as an unchanged regression replay. Its ten audits pass, with the retained
unnecessary-simpa warning. No runtime suite or full Lean replay was run.

## Adaptive unread-cell law — 2026-09-21

Base `78b6d5f84ebc1b013611b81f412717af1faed88c` plus this changeset.
`AspisV8R17/AdaptiveOracle.lean` supplies a generic deferred-decisions bridge
missing from the earlier pathwise provenance result. It uses one complete
finite oracle H, not independent oracles for different protocol components.
A causal policy chooses its next address from the previous address/answer
log. Repeated addresses consequently return the same H value.

Proved: agreement on every cell read by an execution preserves its trace;
updating an unread cell preserves that trace; permuting one cell is an oracle
equivalence; fixing a trace and an unread cell gives a bijection between the
fibers for any two cell values. Thus all joint masses (trace=tr, H(i)=a) are
equal as a varies under a uniform full oracle. A corollary sets i=next(tr),
allowing adaptive next-address selection. These are joint-mass equalities,
valid even for impossible traces, without dividing by a possibly zero trace
probability. For positive-mass traces they support conditional uniformity.

The unread premise refers to the complete prior log from an empty start.
Public prequeries must appear there; a sampler call to a prequeried address
does not meet that premise. Apply the law at its earlier first assignment,
then use retained cache provenance. Fixed private/random coins can parameterize
the policy, but their independence from unread cells must be justified when
averaging over them. The policy cannot inspect unread H through a closure.

First remaining source-specific proposition: refine the combined source and
adversary execution (including commitments, expansion, public prequeries,
absorbs, squeezes and advances) into this causal policy with the same shared
oracle and bounded query accounting. Then charge determinant/sampler events
at justified first assignments, including selection of transcripts and visible
aborts. An arbitrary future-dependent bad predicate is still not admissible.
This generic result is not that source refinement, an adaptive loss bound,
or an end-to-end privacy/soundness theorem.

Six declarations are axioms-audited: run_congr_on_reads and
unread_update_preserves_trace use propext; cellEquiv and traceCellFiberEquiv
use propext/Quot.sound; fresh_cell_counts_equal and
fresh_next_joint_probabilities additionally use Classical.choice.
No new hiding axiom or sorryAx remains. The retained finite-game definition
is reused; this does not assert SHA-256 is an information-theoretic oracle.

Focused cached lake invocation targets `AspisV8R17/AdaptiveOracle.lean` and
its matching object, -j1 -M1800. No production changes or unchanged tests.

| Attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Initial product-equality subtype conversion | 1 | 9.03 | 1462960128 | 0 |
| Corrected five audited declarations | 0 | 3.03 | 1477345280 | 0 |
| Final six including adaptive next-cell joint mass | 0 | 2.89 | 1479507968 | 0 |

The failed audit is rejected. Final compile has no warnings.

## Actual-core cursor differential gate — 2026-09-21

Base `922852d39af704f9713f8d3e3e3017b8416ea9dd` plus this changeset.
New `crates/aspis-core/tests/r17_rejection_cursor.rs` calls the actual
Transcript::challenge_qm31 with a deterministic input-indexed hash backend.
The independent cursor reference scans each limb's next eight candidates
for the first canonical masked word, continuing at the actual consumed
position, and preserves explicit exhaustion. It is an executable counterpart,
not an extraction or formal Rust refinement of RejectionCursor.lean.

Two tests pass, covering every bounded control-flow retry schedule:

* 8^4=4096 successful schedules (0..7 rejections before each of four limbs).
* 1+8+64+512=585 exhaustion schedules (0..3 preceding successful limbs,
  followed by eight rejections on the failing limb).
* Each runs twice with opposite high-bit phases: 9362 cases total. Both
  encodings of masked P are exercised, and accepted examples include 0, 1,
  P-1 and a mixed-byte value. This is not exhaustive over accepted values.
* Every case checks all returned limbs/error, exact squeeze/advance call
  order, block count ceil(consumed/8), and complete post-call state. A second
  call checks that leftover words in the last block are discarded, including
  after exhaustion; it starts at the next block, not the retained word suffix.

This closes the finite schedule-regression gate only. It does not prove
independent oracle outputs, all byte values, arbitrary oracle histories,
or the joint four-limb failure mass. The formal model retains a word suffix;
source composition across separate calls must apply the block-rounding discard
projection, which these tests exercise but do not universally prove. Further
unchanged schedule reruns are not needed; proceed to symbolic source refinement
and adaptive first-assignment probability accounting.

Checked SHA-256 pins:

| File | SHA-256 |
| --- | --- |
| src/transcript.rs | be036d144b9fe0c8119d9f6fdd8ca2167d1379f7d1d785fa2f197200b9f7d119 |
| src/field.rs | 5795495e2fa9ad85e097c2ad96ffc826aaad3c16afc0e0bd00459f9f51068cd8 |
| tests/r17_rejection_cursor.rs | c37fb3eed5c0baa85fba2c76f7871839895fc996b1688b37d556aba17f047631 |

All paths are under crates/aspis-core. Source files are unchanged.
Command: `cargo test --offline --locked --release --jobs 1 -p aspis-core
--test r17_rejection_cursor -- --nocapture`. Guard samples aggregate descendant
RSS every 50ms, terminating above 786432 KiB or 120 seconds. This is a sampled
process-group watchdog, not a kernel/cgroup memory cap; the small focused
local gate stayed well below 8 GiB. Expected work was compilation, not heavy
arithmetic. No full suite or unchanged Lean target was rerun.

| Attempt | Exit | Wall seconds | time-l peak RSS bytes | Swaps | Sampled aggregate peak KiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| Invalid --jobs1 syntax, no compilation | 1 | 0.12 | 17285120 | 0 | 4880 |
| Correct --jobs 1, two tests / 9362 cases | 0 | 1.83 | 140836864 | 0 | 217376 |

Optimized compilation reported 1.31s; tests 0.01s. Existing cfg(solana) and
dead-code warnings remain. rustfmt --check and git diff --check pass.
#print axioms is not applicable to this Rust-only gate; retained Lean audits
are unchanged. Negative regressions and unrelated untracked work are preserved.

## Joint sequential ideal-tape symmetry — 2026-09-21

Base `d0c22b8c212fd1eb0427a4f479e328b4f208ec8a` plus this changeset.
`AspisV8R17/SequentialRelabel.lean` proves a joint distributional symmetry,
not just four marginal symmetries. A list of acceptance-preserving alphabet
permutations assigns one permutation to each requested limb. The full-tape
transformation advances to the next permutation only on acceptance, never
at a fixed word offset. It has a proved inverse using inverse permutations
and preserves total tape length, including on tapes where a bounded scan fails.

The single-scan commuting identity carries the transformed suffix into the
next limb. The multi-scan identity maps the entire returned tuple componentwise
and leaves the final unused suffix unchanged; failure stays none. A fixed-length
List.Vector tape equivalence then invokes the retained FiniteGames coin
reindexing theorem. `joint_uniform_symmetry` is equality of the full laws on
Option (returned-values, unused-suffix) for uniform finite tapes. The theorem
does not drop the suffix or condition silently on successful execution.

Six #print axioms audits pass: the five deterministic lemmas use propext and
Quot.sound; joint_uniform_symmetry also uses Classical.choice. The acceptance
preservation premise is explicit, not a new cryptographic hiding assumption.
No source oracle law is asserted: repeated/cached words need not have this
uniform-tape law. Exact success/failure mass for the multi-limb model, Rust
byte/block refinement, and adaptive shared-oracle selection remain separate.

Focused cached command: earlier lake wrapper and -j1 -M1800, target
`AspisV8R17/SequentialRelabel.lean`, matching cached object. No full replay,
runtime rerun, or production changes.

| Attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Initial recursion/Option simplification | 1 | 7.64 | 1457356800 | 0 |
| Remaining Option bind identity | 1 | 3.06 | 1458683904 | 0 |
| Four deterministic lemmas | 0 | 3.02 | 1472233472 | 0 |
| Tape equivalence, missing local nonempty instance | 1 | 2.43 | 1462812672 | 0 |
| Final six audited theorems and tape equivalence | 0 | 8.18 | 1476067328 | 0 |

Failed-attempt sorryAx results are rejected. The final fixes add the derived
nonempty-vector instance and simplify double inversion; no premise was weakened.

## Sequential word-cursor model — 2026-09-21

Base `4f05c559ad2b549b1e4f9f01000380d3ea5f1bca` plus this changeset.
`AspisV8R17/RejectionCursor.lean` introduces a bounded scan returning both
an accepted value and the exact unused suffix, and scanMany which threads
that suffix through successive limbs. It does not assign each limb a fixed
eight-word slice: the source's cursor advances only by actual attempts.

Five audited theorems compile: projection to the retained firstAccepted
model on take(fuel); evaluation on a rejected prefix followed by acceptance;
the converse decomposition of every success; their iff; and sequential
success giving the exact limb count, acceptance of every returned limb,
and a consumed-prefix/retained-suffix decomposition of length at most
fuel*limbs. For four limbs and fuel eight this is at most 32 words. Failure
is explicit none, with no fallback; these theorems do not give its joint law.

The next missing composition step is the finite-tape counting/bijection
for this variable-length sequential cursor, retaining stopping information
and unused suffixes. Rust decoding, block refills/discard behavior and the
shared-oracle adaptive first-assignment law are separate source obligations.
No ideal tape or cursor theorem here asserts that they are already satisfied.

Focused cached command follows the earlier invocation with
`AspisV8R17/RejectionCursor.lean`, matching object, -j1 -M1800. The initial
broad Mathlib.Tactic import exceeded the Lean memory threshold; it was
removed entirely, not retried with a larger cap. No extra tactic import was
needed. A reserved identifier was then renamed. No production source or
unchanged full regression was run.

| Attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Broad tactic import, memory exception | 134 | 10.86 | 2372042752 | 0 |
| Minimal imports, reserved identifier errors | 1 | 2.09 | 1453850624 | 0 |
| Four scan theorems | 0 | 1.76 | 1472217088 | 0 |
| Final five including sequential composition | 0 | 1.96 | 1478623232 | 0 |

Final #print axioms: scan_projection uses propext only; the other four
use propext, Classical.choice, Quot.sound. No sorryAx or new axioms.

## Single-sentinel ideal instantiation — 2026-09-21

Base `6d875cd144dd9a6eb9cfeb88dcd7dd045d2713e0` plus this changeset.
`AspisV8R17/SingleSentinelSampler.lean` proves that rejecting only the last
element of Fin(q+1) leaves exactly one rejected symbol, gives exact ideal
failure probability `1/(q+1)^n`, and specializes q=2147483647,n=8 to
`1/2^248`. The specialization uses the small base identity 2147483648=2^31
and the symbolic power-of-power law, without enumerating tapes or alphabets.
All three audited theorems use only propext, Classical.choice, Quot.sound.

Re-inspected transcript.rs lines 378–416 and rechecked SHA-256
`be036d144b9fe0c8119d9f6fdd8ca2167d1379f7d1d785fa2f197200b9f7d119`.
The actual implementation masks each decoded word with P, rejects P, advances
a shared word cursor across four limbs, refills after eight words, and aborts
on limb exhaustion. This file proves the ideal single-limb mathematical law,
not the Rust decoding/masking correspondence or the independence of the
remaining words after an adaptively stopped limb. It does not yet prove the
joint four-limb law or any full-protocol privacy/soundness loss.

Focused cached invocation follows the previous section's command with target
`AspisV8R17/SingleSentinelSampler.lean` and matching object, -j1 -M1800.
No unchanged full-suite run or production edit was performed.

| Attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Initial, missing tactic import | 1 | 4.95 | 1451606016 | 0 |
| Imported tactic, redundant proof after congr closed goal | 1 | 1.95 | 1484324864 | 0 |
| Final symbolic specialization | 0 | 1.67 | 1502593024 | 0 |

The source-specific joint sampler/selection premise below remains open.

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
