# C1 query-graph extraction and a bounded noisy-word recovery step

2026-09-08. Continued from `d96f56533bba7763fd907d931df40331f2497de7`
on `research/v8-no-work-100-20260907`. Initial worktree clean. Research
changes only; concurrent main work and all production defaults preserved.

## What changed

The extra-opening oracle has been replaced, in a concrete research experiment,
by an **instrumented raw SHA query log frozen at the C1 commitment boundary**.
The extractor reconstructs the complete C1 word and its root from this log,
before lambda/chi, without receiving the producer's columns, salts, tree,
message table, anchor or witness as arguments.

Two genuine, causally produced payment proofs with non-polynomial committed
C1 words accepted. Both yielded checked payment witnesses from that same
execution's graph. In the harder case, the original interpolation window
failed payment validation and the second window succeeded.

The next falsification succeeded too: corrupting BOTH windows produced an
accepted genuine payment for which that specified extractor returned no witness.
A Gao-style error-correcting fallback recovered a checked witness from the
**same proof ID and commitment**, not from a newly selected favourable proof.
It also recovered all original coefficients in a fixed 16,535-fibre corruption
control. That larger proof rejected; its extraction success is recorded
separately. Sections 4a–4b give the conditional mathematics and limitations.

Lean proves the limited recovery guarantee behind this repair: **at most one
corrupted complete fibre, relative to an encoded 16-column tuple, leaves one
common disjoint window from which the entire tuple is recovered**. The exact
source matrices for both windows have 1,024 pivots in optimized Rust.

This is not a production-readiness certificate. General received-word
recovery, acceptance-to-payment constraints, the source/FS connection,
full-view privacy and matched complete-transaction CU remain required gates.

## 1. Access and causal graph construction

[c1_query_graph.rs](experiments/c1_query_graph.rs) adapts the grammar and
causal traversal in `Pool/V7MerkleQueryExtractor.lean`:

- C1 leaf: `10 71 || value[403] || salt[32]`, 437 bytes;
- C2 leaf: `10 f1 || value[186] || salt[32]`, 220 bytes;
- parent: `11 || left[26] || right[26]`, 53 bytes.

The actual SHA wrapper records concatenated raw inputs, including untyped
entropy/salt/public-binding calls, during each prefix. Recording starts at
the synthetic public-binding hash and ends immediately after the C1 root
is built. It is disabled before extracting and before lambda/chi. Later
prover and extractor hashes cannot backfill the frozen log.

The index retains the first query for each truncated digest and rejects
distinct raw inputs sharing that digest. Identical repeats are harmless.
Each non-default child must resolve to an earlier query than its parent;
missing and forward references remain separate failures. Canonical-default
C1/C2 inputs are included in collision checking, never inserted into the
adversary's causal index. The adapter reconstructs all 262,144 C1 leaves,
then independently rehashes the complete tree and checks the root. It also
checks canonical M31 limbs of all 26 columns.

This last check is stricter than the raw-byte K1.2 word extractor and is a
**conservative extraction failure**, not automatically a small authentication
event: an unopened malformed field encoding need not be rejected by the
actual verifier. Such failures remain in the residual ledger. A robust
decoder may instead need to treat these coordinates as erasures.

The new adapter is C1-only and does not inherit the V7 q16 paired-opening
endpoint theorem verbatim. Its graph is used to generate any needed frontier
internally. No external bundle request supplies the former 111,620 bytes.
That is a change of **extractor access**, not a saving in protocol proof bytes.

### What access this does and does not implement

This is a ROM-style extractor observing the instrumented prover's private
hash queries. It is not a public observer recovering secrets from an on-chain
root or one q22 proof. Private raw queries can contain masks and seed material;
they are retained in process memory only and **not printed, persisted or
uploaded**. Evidence contains only synthetic commitment/proof IDs and counts.

The existing V7 `ExactConcreteK12Bound` has a resource-dependent causal
target/collision argument, but also exact source and supplied-query coverage
obligations. Its q16/stage scheduler and proof grammar are not the new V8
execution. Those files were inspected, not replayed or silently imported as
a bound for this adapter. Actual V8 adversary-machine coupling, restore/fork
resources, retries and complete transcript query coverage remain open.

## 2. Same-execution observations

The final graph-backed four-seed cohort reproduces **all eight previous proof
IDs byte for byte**. Four honest proofs accept; four 9,302-D-fibre corrupted
arms reject at the relation terminal; all eight return checked witnesses.
The semantic producer, actual H/G/D masks, shifted ordinary rows, carried
image check and shifted degree-q query batch remain unchanged.

The two new C1 experiments use fixed seed 1 and predeclared supports, not
search or challenge forcing. They add one to semantic column 0 in all four
slots of a single fibre **before the C1 root and lambda/chi**. H/G/D and later
messages are constructed causally from the genuine semantic producer. The
producer's honest quotient uses its own pre-corruption message coefficients;
the extractor does not receive those coefficients.

| C1 corruption | Proof accepted | Exact received codeword | Checked witness | Candidate used | Body |
|---|---|---|---|---|---:|
| Fibre 256 | yes | no | yes | first window | 39,710 B |
| Fibre 0 | yes | no | yes | second window; first rejected | 39,086 B |

Neither proof queried its changed fibre. The ideal uniform distinct-query
miss probability is exactly `131061/131072 = 0.99991607666015625` for one
fixed fibre. This is a query diagnostic, not an empirical security estimate
or an unconditional acceptance theorem. No payment forgery is demonstrated:
the original valid witness exists and is actually recovered.

These cases refute an overstrong extraction requirement:

```
acceptance -> committed C1 is an exact codeword
```

They do not refute knowledge soundness. Conversely, an extractor that rejects
every non-codeword C1 loses these accepted, recoverable executions. Exact
re-encoding is therefore a diagnostic/classifier here, not a requirement for
returning a witness that the literal payment validator accepts.

Full-degree quotient/chord reconstruction and nonzero denominators are checked
over all 2^20 positions for each produced proof, using the actual source
encoder. Actual query openings use the corrupted received data. These are
finite source checks on these objects, not a universal circle-code port.

## 3. Deterministic recovery theorem and source interface

[ExactC1Recovery.lean](experiments/ExactC1Recovery.lean) uses a full evaluation
matrix E, its selected row matrix A, and a left inverse B. From `B*A = 1`, it
proves:

1. Decoding an encoded message returns that message.
2. Re-encoding the decoded result equals the received word exactly iff the
   received word is in the code.
3. Two encoded messages agreeing on the selected rows are equal.
4. An off-sample change leaves decoded coefficients unchanged but fails the
   whole-word check.
5. For the disjoint windows of fibres 0..255 and 256..511, at most one bad
   fibre leaves one window clean.
6. **The same window recovers all 16 semantic columns**, not merely a
   per-column disjunction allowing inconsistent tuple choices.

No decoder-success, provider-membership or valid-payment premise appears in
the recovery lemma. Its hypotheses are code proximity, the actual common
corruption support, and the two inverse identities. The real encoder's
linearity/basis correspondence and concrete inverse certificates are still
source-bridge obligations: Rust constructs both matrices with
`CircleEncoder::encode_c1_basis_value` and checks full elimination, but this
is not a kernel certificate of the concrete matrices or an automatic Rust
translation.

The extractor tries each whole-table candidate in order and calls the literal
`extract_checked` payment/context/transition validator. A different valid
witness would count as success. Equality with the original synthetic witness
is asserted only after return. Failure of both candidates remains extraction
failure; it is not proof that no valid witness exists. The harness currently
aborts that test case on exhausted candidates; this is a retained failure,
not a path discharged by the theorem.

**Limits:** the guarantee is for one corrupted fibre, not the near-gamma
16,535-fibre own-support mismatch allowance, and not arbitrary accepted
received words. Adding a second window does not justify an uncharged family
union or a global acceptance bound. Even two corrupt fibres can touch both
fixed windows; no general error-correction claim is made.

## 4. Adversarial checks and measurement scope

Focused controls cover missing root/preimage, forward reference, exhausted
walk fuel, repeated queries, canonical defaults, malformed tags/lengths,
noncanonical fields, a deliberately colliding test hash and late query
insertion. For a fixed four-leaf tree, **all 5,040 query orders** are tested;
exactly the 80 causal orders succeed. This is exhaustive over permutations
of that graph, not over adaptive adversarial strategies.

An authenticated single-value change outside the first matrix's sample has
unchanged sample coefficients and fails the full-word test. The payment C1
controls above then advance that diagnostic to genuine accepted executions.
The first-window control demonstrates actual candidate failure followed by
successful bounded fallback, without supplying the original trace to either
candidate constructor.

| Resource | Measured / exact scope |
|---|---:|
| Raw instrumented SHA calls per C1 prefix | 1,051,764 |
| Distinct raw inputs | 789,620 |
| Raw query input payload | 238,287,374 B |
| Full C1 leaf payload | 114,032,640 B |
| Full tree digest payload | 13,631,462 B |
| Walk fuel / visited nodes | 524,287 / 524,287 |
| Default leaves expanded in payment runs | 0 |
| Index hashes, including 38 default inputs | 1,051,802 |
| Independent root-recomputation hashes | 524,287 |
| Two retained inverse matrices | 8,388,608 B payload |
| One candidate solve, all 16 columns | 16,777,216 M31 multiply-add pairs |
| Candidate-selection limit | 2 candidates / 2 validator calls |
| Final eight-arm harness | 170.94 s; 1,046,216,704 B peak RSS |
| C1 fibre-0 harness | 36.08 s; 625,180,672 B peak RSS |
| Final Lean leaf / axioms audit | 15.90 s; 2,814,033,920 B peak RSS |

All recorded swaps are zero. Candidate-selection counts exclude repeated
validation for assertions/proof-root coupling; timings include those extra
checks, full commitments, actual semantic proving, graph reconstruction,
whole-word diagnostics and full-domain chord checks. The raw-log/trees are
extractor storage, not network downloads. Vec/index allocator overhead is
included in measured RSS but not the payload rows. No hash-rate/CU extrapolation
is made: the arithmetic is optimized Rust, while SHA uses the pinned cached
debug dependency. No new SBF/full-transaction measurement was performed.

The graph traversal is height/fuel bounded. Indexing is bounded in terms of
the supplied raw-query count and byte volume, not an unlimited-adversary
guarantee; the current logger has no independent allocation cap. A production
experiment must enforce its declared oracle/memory budgets and classify
overflow rather than assume the honest measured query count limits attackers.

There are no protocol message changes. The maximum body remains
`697*16+52+24+22*621+2*296*26 = 40,282 bytes` (largest observed: 39,814).
Extractor work gives no security bits and is not charged as verifier CU.
Inherited dense transposition and 16,384-byte public-weight hashing remain.

## 4a. Fixed windows falsified; same-proof error correction

Predetermined C1 column-0 corruptions add one to all four slots of fibres 0
and 256, before the commitment and early challenges. Neither fixed window
returns a table passing the literal payment validator. The proof nevertheless
accepts with both fibres unqueried. Its ID is
`a9b1e6f6e26f9a0321804541c76593af3c5a11a8a0096e3ddc5bd4331e8ef55f`.
This refutes coverage of the two-window extractor, not knowledge soundness:
the synthetic execution has a valid witness.

[c1_gao.rs](experiments/c1_gao.rs) adds a bounded extractor-only alternative.
For circle points, put z=x+i*y in CM31. The actual tensor basis is
`y, T1(x), T2(x), ..., T256(x)`. Its products have Laurent exponents within
[-512,512]. Multiplication by z^512 therefore embeds evaluations into an
ordinary degree-at-most-1024 polynomial. The ambient RS dimension is **1025**,
not 1024; membership in that ambient space alone is insufficient.

The decoder uses polynomial interpolation and extended Euclid, then checks
exact division, degree, error radius, M31 descent, the actual source encoder
and a full-word common-fibre distance cap. Its first control uses 1,153
evaluations and corrects up to 64 symbol errors. It recovered the two-fibre
case's eight altered samples; the same root, proof ID and 39,554-byte body
then had `accepted=true, checked_witness=true`. No extra prover messages or
verifier checks were added. Recovery took 0.733 s; the whole harness took
35.75 s and 624,295,936 B peak RSS, with zero swaps.

The algorithm follows the unique-decoding construction in Gao's
[author-hosted paper, Algorithm 1a and Theorem 3.3](https://www.math.clemson.edu/~sgao/papers/RS.pdf),
published in 2003 ([author bibliography](https://www.math.clemson.edu/~sgao/WEB/publications.html)).
Access on 2026-09-08 was through indexed primary-paper sections; direct PDF
retrieval timed out. Its decoding guarantee applies to distinct-point RS
evaluations inside the stated radius. It does not supply Aspis's encoder,
authentication or payment correspondence. The implementation passed 2,688
restricted degree-two/three-error cases, zero input and repeated-point
controls. These are not exhaustive tests over adversarial strategies or a
kernel-checked decoder implementation.

### Large corruption control, without searching for acceptance

The next declared support is the first 16,535 complete fibres, with the same
column-0 increment. A separate extractor sample selects 513 distinct fibres
using fixed reproducibility coins, giving 2,052 evaluations. The ambient
decoder radius is 513 symbols. The run sampled 32 corrupt fibres (128 errors),
recovered the original coefficients, verified a common discrepancy set of
exactly 16,535 fibres, and returned a checked witness. Recovery took 1.112 s;
whole harness 37.21 s, peak RSS 655,818,752 B, swaps zero. It checked 2,101,248
source basis evaluations. This is a finite encoder check, not a universal
source translation. The fixed proof hit one corrupt fibre and rejected at
the relation terminal; no subsequent seed was searched.

An earlier run stopped at an overly strong fixture assertion comparing the
first recovered table to the producer's whole table. That first candidate
already yielded a valid witness: constant corruption of its entire sampling
window changed an unused coefficient. The corrected harness keeps literal
validation authoritative, reports table equality separately, and executes the
large Gao control even if the earlier candidate succeeds. The failed run was
29.37 s / 600,424,448 B / exit 101 / zero swaps. Its assertion rendered a
synthetic table; that table is deliberately not retained in evidence. This
was a fixture error, not a rejected valid witness or a verifier bypass.

## 4b. A conditional recovery bound for the near-gamma C1 support

Suppose the fixed, canonical received C1 is within B=16,535 COMMON fibres of
a source-code tuple. This is the near-gamma dense branch's own-support radius,
not a premise established for every accepted execution. Sample 513 fibres
uniformly without replacement using independent private extractor randomness.
If at most 128 sampled fibres are bad, all 16 columns have at most 512 symbol
errors and are uniquely decodable in the 2,052-point, dimension-1,025 ambient
RS code. One common bad set controls every column, so no 16-target union is
required. Thus the conditional decoding-failure bound is

    sum(j=129..513) choose(16535,j)*choose(245609,513-j)
    / choose(262144,513).

[Exact rational arithmetic](c1-sampling-results.json) gives 137.7548064779
display bits and proves the value is below 2^-137. The script cross-checks
1,438 small parameter cases against literal subset enumeration. Monte Carlo
does not supply this bound.

For an ideal uniform draw stream with a 4,096-draw cap, failure to collect 513
distinct fibres requires at least 3,584 repeats. Before completion each repeat
has conditional probability at most 512/262144. Union over subsets of repeat
times bounds exhaustion by `2^4096*(2^-9)^3584 = 2^-28160`. Relabelling the
domain preserves every draw probability, collision pattern and stopping rule;
therefore every 513-subset has equal conditional output probability. The sum
of exhaustion and hypergeometric failure is still below 2^-137. The concrete
prototype uses a fixed SHA seed only: it does NOT establish that ideal law.

There is also a useful causal uniqueness fact. Two original-code columns each
within B fibres of the same word would agree on at least T-2B fibres. Since
`2*16535+256=33326 < 262144`, the existing overlap/nearest-anchor argument
forces equality. Consequently a close full tuple constructed after C2 has a
unique C1 projection determined by the C1 word wherever such a projection
exists. This does not move an arbitrary post-challenge tuple backwards in
time, does not erase the small-Good branch and does not prove existence at
every C1 prefix. Subfield descent still needs its actual source bridge.

The remaining theorem ports are explicit: universal Laurent/source encoder
embedding; total canonical/erasure handling; algorithmic Gao correctness and
runtime; the common-radius premise from the stated near event; and the
semantic constraints making the recovered table yield a checked witness.
Until these are connected, the numerical result is a conditional extractor
calculation, not an additional achieved V8 security term. It cannot cover the
far/root-product regimes or accepted graph/provider/replay failures by itself.

## 5. Correct event and production-readiness decision

Let X_graph_checked be the graph walk followed by the bounded candidate/actual
validator procedure in this explicit access model. The residual event remains
`A AND NOT X_graph_checked`, with first-failure precedence:

1. Missing query-log access, budget/fuel exhaustion, or replay/source mismatch.
2. Graph, raw grammar, root or canonicality failure.
3. Both recovered candidates AND the bounded Gao fallback fail actual
   payment/runtime/nullifier/transition validation. The two-window-only
   failure above is retained as a regression of the weaker extractor.

Success contributes zero even when C1 is non-polynomial or outside an earlier
radius classifier. The real FS extractor must also be coupled to this access
model; zero rewinds in this experiment is not a completed FS lifting theorem.
K13/K14/provider-none, cached/advance mismatches and scalar-versus-pointwise
acceptance remain in the global accounting rather than being discarded.

The [exact ledger](query-graph-results.json) leaves all unproved error terms
null. The existing near-gamma ceiling is reused only for its stated
bad-binding event. No historical 396430 numerator or duplicate relation-repair
charge is added; no positive grinding contribution or invented toolchain
probability is assigned. Privacy is a separate full-view simulator obligation.

| Required production gate | Current status / next necessary evidence |
|---|---|
| Global raw accepted-extraction error <=2^-100 | Open: general received-C1 recovery and semantic/payment coverage |
| Actual resource-bounded FS theorem | Open: V8 source/scheduler/query-log coupling and full accounting |
| Full-view ZK | Open: simulation of repaired row/image/OOD/final/query view |
| Same payment/context/settlement execution | Executed synthetic transfer slice; universal residual implication and actual account caller bridge open |
| Proof body <=40,282 | Unchanged model and parser; exercised proofs fit |
| No complete-transaction CU regression | Unmeasured for complete repaired V8; all four matched shapes required |
| Deployable source/SBF and malformed-path assurance | Research kernels/fixtures only; complete integration remains |

Thus **V8 is not production-ready on the present evidence**, and this work
does not activate it. The new result is a real access/recovery advance plus
accepted non-polynomial controls, not a new security level. Earlier rejected
same-support, image-kernel and row-cancellation shortcuts remain rejected.

**Decisive next experiment:** connect the Laurent/RS recovery interface to the
actual circle encoder symbolically, then exercise noncanonical C1 coordinates
as totalized values or erasures in that same authenticated graph. This targets
the present adapter's unconditional canonicality rejection and makes the
conditional near-radius recovery guarantee usable beyond canonical controls.
Keep the far accepted-C1 and semantic-to-witness obligations explicit. QM31 q22
still merits this focused work because the new decoder spends only extractor
resources; it adds no proof bytes or verifier work. Failure of this route
would not establish general impossibility. No size relaxation is authorized.

Reproduction commands, pins, phase-specific evidence and audits:
[query-graph-evidence.json](query-graph-evidence.json).
