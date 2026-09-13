# R8 witness-retaining paired-commitment hop

Date: 2026-09-13.

Status: **universal finite same-provider hop proved; selected source grammar
instantiated; V8 source-to-model trace and first semantic-message transport
remain open**.

This milestone does not prove full V8 privacy. It does not repair the known C1
separator, construct a public-history-only payload provider, justify the real
seed expansion as ideal coins, or authorize publication.

## Source lock and supplied regressions

The reviewed archive is
`aspis-v8-paired-commitment-pack-reviewed-20260913.zip`. It contains
`CODEX_PROMPT.md` (not the requested `CODEX_TASK.md`) and identifies the same
task and source revision. All 38 entries in its `SHA256SUMS` verified. The
working branch and every non-null source blob pin equal
`b0c738eefb0026cdd6ed647c68dd527395c78294`. Two ledger documents have null
blob pins and remain explicitly unpinned.

The supplied reference verifier passed 63 Python tests, 128 coupled episodes,
9,334 public-equality checks, and all 9 exact finite-distribution cases with
both marginals and aborts retained. These are reference-model results, not a
theorem or actual-prover refinement.

The research-only Rust source KAT passed 3 tests against the real core hashing
and frontier functions. It covers the literal leaf and parent grammar and all
255 nonempty opening subsets of an eight-leaf tree. It does not model the V8
prover chronology.

## What Lean proves

`Table`, `ShadowTable`, and `ForwardHop` give a forward-only construction:

- deferred leaf inputs are added only while absent from both tables;
- ordinary queries use the actual cached answer on a hit and a fresh answer on
  a miss;
- paired materialization installs both full 256-bit reserved answers
  atomically or takes an explicit conflict branch;
- already exposed history is never rewritten;
- repeated successful materialization is immutable;
- an execution trace, not an assumed `agrees` predicate, preserves the
  shadow-table invariant and equal public observations before Bad.

`Marginals` proves both exact uniform marginals for all four cached/fresh rows
and for the full fixed-slot-tape joint run. After Bad, each experiment retains
its own actual output; only agreement stops.

`finite_witness_retaining_commitment_hop` constructs the joint view, returns
both marginal equalities, and bounds every Boolean observation gap by the bad
mass whenever the supplied source execution constructs the forward trace on
nonbad tapes. The payload provider may retain the witness. Consequently this
is a conditional compiler/wrapper theorem, not a public simulator lemma.

`SaltCounting` derives rather than assumes the ideal salt loss. A
coordinate-fiber cap says that after all other salts and allowed auxiliary
history are fixed, at most `q` values of one still-hidden salt trigger that
coordinate's probe event. Lean proves:

```text
probeCount <= |Slot| q |Salt|^(|Slot|-1)
collisionCount <= |PairIndex| |Salt|^(|Slot|-1)
badCount <= (|PairIndex| + |Slot| q) |Salt|^(|Slot|-1)
```

and the exact uniform-mass corollary obtained by dividing the last numerator
by `|Salt|^|Slot|`. For unordered distinct slot pairs,
`|PairIndex| = n(n-1)/2`, this is the sharper ideal-IID form
`n(n-1)/(2S) + nq/S`; it is no larger than the handoff's conservative probe
term `nq/(S-n-q)` when `n+q<S`. The combinatorial pair-cardinality adapter and
the actual source query cap are not silently instantiated.

No theorem in this directory depends on `sorryAx`. Reported axioms are the
standard Mathlib foundations `propext`, `Classical.choice`, and `Quot.sound`
as applicable.

## Literal selected source boundary

The source-exact local adapter records:

- C1 packed payload: 104 M31 limbs, 403 bytes;
- C2 packed payload: 48 M31 limbs, 186 bytes;
- salt: 32 bytes, shared by the C1/C2 record for one fibre;
- leaf inputs: `0x10 || 0x71 || c1Packed || salt32` (437 bytes) and
  `0x10 || 0xf1 || c2Packed || salt32` (220 bytes);
- parent input: `0x11 || left26 || right26` (53 bytes);
- the verifier separately checks every packed limb `< P` and every unused bit
  zero before authenticating the paired record.

The prover constructs C1, absorbs its root, and samples `lambda, chi`; it then
constructs padded H1 and `[H1,G,D]`, builds and absorbs C2, and only then forms
the first semantic polynomial. Opened records serialize C1 packed bytes, C2
packed bytes, and the same derived salt together, after the transcript has
selected the queries. The paired verifier hashes both records and traverses
both frontiers in one interleaved topology.

## First semantic-message cut

The first semantic message remains exactly after the commitment hop. At round
zero the source evaluates 28 samples, each summing the selected semantic
oracle over the remaining Boolean coordinates, interpolates the degree-27
polynomial, writes and absorbs it, then samples the next challenge. R7 already
shows that this observation is fixed-affine in the remaining H1 pad only after
the prior state, C1/C2 roots, challenges, G, mask-only values, and offsets are
fixed. The same H1 correction must be reused for later point/OOD/final/query
observations.

## First remaining source-specific obligation

Construct and prove the refinement from the selected source's complete shared
SHA-256 call trace to `ForwardTrace` and the salt-counting coordinate-fiber
premise. It must start before C1, retain the pre-existing oracle table across
C1, C2, the transcript, retries, and openings, and explicitly replace the
deterministic `derive_v7_leaf_salt`/field expander outputs with an ideal IID
salt/pad tape under a charged seed-expansion hybrid. It must count every
probe-capable ordinary hash query before first salt disclosure, show the
concrete cap `q`, and prove that 26-byte digest truncation and interleaved
frontier verification are projections of the reserved full 32-byte answers.

Only after that refinement is available can the first semantic-message cut
consume the R7 incidence correction. The next algebraic endpoint must then
construct one causal joint provider for the C2 payload/root and first semantic
polynomial while preserving C1 history. The existing C1 separator prevents
turning this same-provider result into an unconditional public-history-only
provider theorem.
