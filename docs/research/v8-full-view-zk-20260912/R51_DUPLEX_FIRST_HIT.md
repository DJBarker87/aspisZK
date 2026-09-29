# R51: duplex framing, fresh pairs and the first-hit boundary

Base `e5d3c322dd27c3c90b5b486a4ceea9db74564d2e` (R50).
Branch `research/v8-r51-duplex-first-hit-20260929`.

## Result

**27 new Lean theorems and three equivalence constructions compile, with
30 standard-axiom audits.** The actual Rust transcript passes new framing,
memoization and failure controls. This establishes a byte-framed one-step
bridge and a conditional fresh-pair law, **not** the full source joint law.

No protocol, production verifier, mask, negative privacy regression or wire
change. No new SBF measurement: retained CU remains **1,620,236 / 1,621,719**,
and both actual 1M-cap runs exhaust. Neither full privacy nor the CU target
is complete.

## What is proved

The source `Transcript::squeeze_block` has two addresses, both selected from
the **pre-step** 32-byte state:

```
out       = H(state || 0x01)
nextState = H(state || 0x02)
```

The advance address does not use `out`. The proof represents these as actual
byte lists rather than giving each oracle user a disjoint typed namespace.
The two frame families cannot collide with one another. Within either
family, equal addresses imply equal states. Transcript absorb frames have
at least 34 bytes; grinding frames have 41. They cannot equal these 33-byte
addresses. This does **not** exclude arbitrary external oracle queries or
every other hash family in the repository.

For any fixed prior causal oracle trace, if both selected cells are unread,
independently permuting their answers preserves that trace. The explicit
two-cell bijection proves equal joint output/state fiber counts and uniform
probabilities in a **finite uniform-oracle model**. It does not assume two
separate oracles. The byte-address bridge applies that same bijection to a
32-byte-output step; it is not a claim of a uniform distribution on the
infinite set of all byte-list oracle tables.

The next pair is fresh exactly when its state's two addresses were absent
from the old trace and its state differs from the previous state. If advance
returns the previous state, both subsequent addresses and answers repeat.
The model retains that case, rather than resampling a previously used cell.

For a fixed list of `Q` prior addresses, at most `Q` 32-byte states can hit
one of those addresses. The injection proof uses each address's first 32
bytes as a conservative support; no enormous finite state space is reduced.
The state space has cardinality `256^32`. Consequently an **independently
uniform state**, with that prior list fixed, has hit fraction at most
`Q / 256^32`. This is a one-step counting bound, **not a bound for the whole
source execution, known/adversarially selected states or publication**.

## Why prior reads cannot simply be called rare

A caller that knows a transcript state can deliberately query
`state || 0x01` before the transcript calls `squeeze_block`. The later call
is then a cache hit with certainty, without finding a hash collision.
The Rust controls exercise this for both squeeze and advance addresses.

Thus the next proof must track a challenge's **first oracle read**, not
declare every transcript call fresh and charge all exceptions to a birthday
bound. Known-address lookahead, nonce search and selection may move that
first read earlier. Repeated prefixes must replay their recorded answers.
Any query/attempt multiplicity and stopping/publication loss must be proved
for the selected experiment, not hidden inside the fresh-pair premise.

The source comment that advancement means an input is never rehashed is not
an unconditional mathematical invariant. Repeated states and external prior
reads are real model cases. This observation is not a demonstrated practical
SHA collision or a newly established protocol attack; it identifies exactly
where the probability proof needs more than deterministic domain separation.

## Executed source controls

The new release binary imports the pinned **actual** `aspis_core::transcript`.
Its hash callback is an intentionally scripted, memoized table—not a random
oracle and not a replacement production backend.

| Check | Executed result |
|---|---:|
| Advancing squeeze/advance pairs, same pre-state framing | 64 |
| Repeated-state, repeated-address/answer control | 1 |
| External prior read of squeeze or advance | 2 |
| Packed/hashv versus split absorb, including 158/159-byte boundary | 15 |
| Bounded QM31 and q22 failure controls | 2 |
| Repeated QM31 failure reuses both cells | 1 |

All checks passed with release optimization, overflow checks, offline locked
Cargo and two build jobs. The q22 negative consumes eight pairs, repeatedly
reading the same two addresses and returning the explicit accepted-count
failure. No failure is silently discarded.

The source manifest retains all 197 parent pins; only the test-bin Cargo
entry changes and one new test file is added. The source transcript hash is
`be036d144b9fe0c8119d9f6fdd8ca2167d1379f7d1d785fa2f197200b9f7d119`,
identical to the current worktree. This is executable source evidence and a
source-shaped Lean model, not Rust/Aeneas extraction or an exhaustive proof
of all transcript byte/word operations.

## Proof and resource receipts

| Leaf | New theorems | Axioms audits |
|---|---:|---:|
| `DuplexFrames` | 9 | 9 |
| `DuplexFreshPair` | 5 | 7 |
| `SourceDuplexStep` | 9 | 10 |
| `UniformStateFirstHit` | 4 | 4 |

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r51_evidence.py
```

Gate: **27 artifacts, 272 pins, 263 successful cached objects**. The four
new leaves total **6.36 s** wall time, peak RSS **3,259,440 KiB**, exit 0,
swap 0. Every audited declaration uses only `propext`, `Classical.choice`
and/or `Quot.sound`. Two unchanged missing dependencies were compiled once;
no package-wide replay was used.

NUC Lean scopes: high/max **3G/5G**, swap max 0. Release source scope:
**5G/7G**, swap max 0; maximum simultaneous reservation 12 GiB. Build:
**18.62 s**, peak **519,256 KiB**. Control execution: timer reports **0.00 s**,
peak **2,112 KiB**. Failed focused attempts and the rejected staging-count
preflight are retained. Concrete finite-state elaboration was replaced by
a generic injection lemma, not a raised recursion/memory limit.

## First remaining proposition

Construct a source-causal **first-read/memoized coupling** for the selected
complete experiment: transcript, commitments, expansion, permitted external
queries, and nonce/attempt policy. It must retain the complete observation
trace and explicit failure outcomes, sample only genuinely unread cells,
replay cached cells, and justify the law at each first read. Prove the actual
loss for state collisions and for selection/lookahead separately. A premise
that simply assumes all transcript squeeze addresses fresh is insufficient.

Then connect the exact bounded QM31/OOD and q22 word/block algorithms to
that coupling, including q22's completion-detection block, and establish
the joint law needed to apply R50's fixed-root polynomial family after later
query selection. There is still **no source `819/|QM31|` privacy bound**.

Full joint H1/G coverage, the Schur target `b - B A^-1 a`, all semantic cuts,
coherent pre-beta quotient extraction, seed/commitment hops, word/optimized
kernel refinement, and failure/retry/publication simulation remain release
obligations. No new hiding assumption or global security conclusion is added.
