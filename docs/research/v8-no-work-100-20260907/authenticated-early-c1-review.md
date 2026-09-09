# Authenticated C1 fixed at an early oracle prefix

Research checkpoint: `3a0b144dee108041320a23850ab4478444a74745`.
Read-only cache/main checkpoint during all recorded runs:
`9b84a1e27d2159ca21fc4ed9dad21b5a9e87daf1`.
No existing Lean/source files, production paths, protocol parameters or wire bytes changed.

## Result

The new bridge no longer starts by postulating a total C1 word fixed before
the early challenges. It constructs one from a finite ordered **query/answer
prefix and C1 root**, using V7's partial-path resolver and a fixed default for
unresolved leaves. Its dependence only on answers present in that prefix is
kernel-checked. A root without this prefix is not an oracle-access model.

For an actual same-root C1 opening whose bottom-up hash calls are in the
shared log, the proved alternatives are:

1. Its exact packed leaf and salt equal the prefix-completed word's leaf.
2. A later input hashes to the first unresolved target selected by the early
   resolver at that position.
3. Two distinct raw inputs in the shared log collide in their 208-bit outputs.

The second alternative is retained even if the opening position is chosen
after later challenges. All possible first-unresolved targets form **one set
fixed by the early records/root**, of cardinality at most **262,144**. Any
position-specific late hit is proved to hit that same set. This is a
deterministic reduction, not an asserted hash probability.

For a possibly late width29 tuple, a set `S` of at least 245,609 distinct
fibres with canonical, authenticated C1 values agreeing with its first 26
encoded components now gives:

```
fixedEarlyC1(early records, C1 root) = some(late tuple's C1 projection)
OR a later first-target hit at some fibre in S
OR a shared raw-208-bit collision.
```

There is no premise that every early path resolves, no assumed candidate
membership, and no assumption that a root has a unique total word. The
support may be a proper subset. The result consumes the existing exact
encoder/fibre cap and original optional `earlyC1` object; it does not replace
that object with a more convenient completion chosen later.

It does **not** establish that accepted V8 executions provide such a set of
authenticated values, that a width29 tuple exists, or that the returned C1
tuple satisfies payment constraints. One q22 proof contains 22 opened fibres,
not 245,609. The larger support here is an explicit extractor/analysis access
condition; no extra openings have been added to the wire.

Moreover, the earlier near-gamma own support is defined for a totalized field
word. Unopened noncanonical bytes can contribute zero-valued coordinates to
that word. Its cardinality alone therefore does not supply this theorem's
stronger **successfully parsed, authenticated** support. That source/parser
coupling remains an explicit obligation, not an inferred acceptance fact.

## Checked endpoints and V7 reuse

| New endpoint | What is derived | Remaining premise/boundary |
|---|---|---|
| `AuthenticatedEarlyC1Prefix.lookup_agrees_on_advertised_input` / `frozenView_agrees_on_prefix` | First-answer lookup agrees with any oracle extending the recorded answers | Records must be actual complete early shared-oracle observations for the intended experiment |
| `prefixWords_eq_actual_view` | Prefix canonical word is identical under any such later oracle extension | No claim that a later extraction run or its whole word equals this completion |
| `accepted_opening_prefix_or_late_target_or_collision` | Literal one-opening projection or concrete late-hit/collision alternatives; actual authentication path constructed from bottom-up siblings | Same-root path acceptance, its calls in the shared log, early-prefix inclusion/answer consistency |
| `AuthenticatedEarlyC1Projection.projected_canonical_fibre_matches` | Root-bound leaf projection plus **successful canonical parser** gives the actual V7 encoder's four fibre evaluations | Claimed codeword evaluations must match these disclosed canonical values; zero-default decoding is not substituted for parser success |
| `authenticated_support_identifies_or_bad` | Such authenticated support fixes the first 26 columns of a late width29 tuple to the original early optional object | Obtaining the support and tuple from accepting executions remains open |
| `AuthenticatedEarlyC1Targets.allTargets_card_le` | At most `2^18 = 262144` distinct early first-target digests across the entire C1 domain | No assumption concerning later opening selection |
| `opening_late_hit_yields_whole_domain_hit` / `accepted_opening_prefix_or_shared_failure` | A later selected opening's bad case hits that one early target set, or a shared collision occurs | Numeric ROM/FS probability and actual source/replay event injection remain open |

Reused V7 declarations include `resolvePath_eq_of_agree_on_log`,
`extractPrefixFixedWords_eq_of_agree_on_log`,
`resolvedC1Path_yields_covered_prefix_opening`,
`c1_covered_opening_is_projection_or_raw_collision`,
`authenticatingPath_of_bottomUpOpening`,
`firstUnresolvedTarget_yields_later_hit_or_collision`, and
`c1_received_of_exact_projection`. The prior V8 exact C1 identification
consumes the V7 original circle encoder and complete-fibre overlap cap.

The fixed sixteen-opening V7 wrapper is **not** used. The new path theorem is
per opening and has no q16 limitation. The underlying C1 byte grammar still
matches the research prototype: `0x10 || 0x71 || packed[403] || salt[32]`,
208-bit SHA prefix, tree depth 18, and parent input
`0x11 || left[26] || right[26]`. Source inspections:
`crates/aspis-core/src/v7_merkle208.rs`,
`experiments/relation_callback.rs` (`opened_values_reference`),
`experiments/performance.rs` (C1 tree before `start` derives lambda/chi), and
`experiments/authenticated_c1.rs` (extractor-side canonical parser/Merkle check).
This is source-shaped mathematics plus source inspection, **not** a translated
Rust refinement of the q22 minimal-multiproof verifier or its hash-call log.

## Why the prefix model is not a late totalization

`AnswerPrefix` stores literal input/208-bit-answer pairs. `frozenView` returns
the first answer for an input present there, and a fixed zero answer otherwise.
The V7 resolver only consults inputs present in the supplied log; the view
congruence proof prevents unknown/future answers from influencing the
completed word. Unresolved leaf bytes are fixed zeros. A canonical all-zero
leaf can legitimately occur; noncanonical packed limbs cannot pass the
new authenticated-coordinate parsing premise merely by being totalized to
zero.

This deliberately does not use the complete graph extractor as an early
source by fiat. Its canonical-default-subtree digests can evaluate a supplied
total hash view outside the chosen early log. The partial-path completion
avoids that dependency and makes missing paths visible in the event theorem.
It needs no new oracle queries to hash canonical-default subtrees.

The early prefix must include **all** relevant shared-oracle prequeries, not
only typed Merkle inputs. The argument does not move a prefix recorded before
q22 backwards to before lambda/chi. The actual V8 operational model must cut
the records at the C1 fixing boundary, prove answer consistency, and map
accepted supplied-path calls into the shared log. No proof here establishes
those scheduler/source premises.

## Events, resources and the next ROM bridge

`WholeDomainLaterHit(view, records, root, fullLog)` is exactly an input in the
full log but not the early raw prefix whose 208-bit answer belongs to the
early whole-domain target set. Hash collisions retain both distinct raw
inputs and their log membership. These alternatives are shared events: do
not multiply the collision term by every opening or add a q22 target union
on top of the already whole-domain target-set event.

No numerical error term was added to the security ledger in this work.
The existing V7 `V7BudgetedAdaptiveTargets.budgeted_causal_hit_count_le`
provides the generic finite count
`budget * targetCap * |Output|^(steps-1)` for causally selected target sets.
`V7Tag73K12Merkle208PrefixProjection` proves the uniform 256-to-208 output
projection. These source statements were inspected, not replayed or
instantiated here. Their existing **32-target / 468-call V7 specialisations
do not match this experiment**.

The decisive next authentication experiment is to construct the actual
early-C1-prefix-to-later-query causal target tree with `targetCap=262144`,
inject `WholeDomainLaterHit`, and charge all fresh calls/retries/restorations
in the chosen resource regime. Only after that injection and the proper
uniform conditional law would the generic target contribution simplify to
`Q * 262144 / 2^208` for `Q` charged fresh answers. This is a proposed
instantiation, **not a completed V8 probability theorem**. Shared raw collision
accounting, actual FS adversary resources and extraction-fuel failures stay
separate. No grinding/work contribution is used.

The canonical completion and `earlyC1` are mathematical analysis objects;
`earlyC1` uses noncomputable choice. The literal list resolver repeatedly
scans its prefix and is not claimed to be an efficient implementation.
No new Rust decoder, rewind extractor, prover-time measurement, peak-RAM
measurement or SBF benchmark was run. The existing 256-fibre authenticated
interpolation control is not this 245,609-fibre support access contract.

## Wire, privacy and residual security

The maximum body remains exactly
`697*16 + 52 + 24 + 22*621 + 2*296*26 = 40282` bytes. These are extractor-side
definitions and proofs only; no verifier messages, hash calls, rounds or CU
have changed. This does not establish CU parity or full-view ZK.

Near-gamma existence/support and the 105.145190-bit restricted event retain
their old scope. To reach payment knowledge the missing chain still includes
accepted-execution recovery coverage, real authenticated-opening/replay
access, early C1 semantic/copy bindings, tuple-to-witness validity, and source
correspondence. In particular, a late tuple's correctly identified C1
projection alone is not a valid payment witness.

## Reproduction and evidence

Run from the research worktree, with the existing cache available and an
exclusive local Lean slot:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_authenticated_early_c1.sh /tmp/auth-prefix.log AuthenticatedEarlyC1Prefix
bash docs/research/v8-no-work-100-20260907/experiments/run_authenticated_early_c1.sh /tmp/auth-projection.log AuthenticatedEarlyC1Projection
bash docs/research/v8-no-work-100-20260907/experiments/run_authenticated_early_c1.sh /tmp/auth-targets.log AuthenticatedEarlyC1Targets
```

The script derives `LEAN_PATH` with `lake env`, then directly executes the
same pinned Lean binary with `-M7000` to avoid keeping an extra Lake parent
resident. A separate process-tree guard stops the exact job above 7 GiB
aggregate RSS. It checks the full imported Aspis source closure against the
research pin and read-only cache before/after every successful leaf. The
logs contain **87** distinct Aspis source/olean pairs plus the eight prior
research source/olean pairs, not merely the top-level imports.

Lean 4.32.0 (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`), Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`; Mathlib Tactic olean SHA256
`55ee2345729e8a4d379de3bce14ea18b14fbfdc259cf2653fadf4bf3a46876d8`.

| Recorded log in `experiments/` | Exit | Wall seconds | Peak RSS bytes | Swap | Result |
|---|---:|---:|---:|---:|---|
| `authenticated-early-c1-prefix-v1.log` | 1 | 5.54 | 5510823936 | 0 | List-equality orientation and tactic layout errors; retained failure |
| `authenticated-early-c1-prefix-v2.log` | 0 | 4.30 | 5678972928 | 0 | Prefix/locality and actual opening alternative checked |
| `authenticated-early-c1-projection-v1.log` | 1 | 2.97 | 5506564096 | 0 | Reserved identifier `matches`; retained failure |
| `authenticated-early-c1-projection-v2.log` | 0 | 3.12 | 5659131904 | 0 | Canonical fibre and authenticated support-to-early-C1 checked |
| `authenticated-early-c1-targets-v1.log` | 1 | 3.00 | 5514379264 | 0 | Missing explicit list argument; retained failure |
| `authenticated-early-c1-targets-v2.log` | 0 | 3.06 | 5659017216 | 0 | Whole-domain target cap and shared-event reduction checked |

All ten retained theorem audits use only subsets of
`propext`, `Classical.choice`, `Quot.sound`. No retained theorem depends on
`sorryAx` or a new axiom. Failed logs naturally show temporary Lean error
placeholders; they are not claimed proof artifacts.

Final source/olean SHA256:

| Leaf | Source | Olean |
|---|---|---|
| `AuthenticatedEarlyC1Prefix` | `a4feb97b426d0251f42bd7315d5fccf8a6c0264c48950fd51bb62d11e993dc9e` | `50d5fd7cc93aab0f8e28901a3481c5dbe7ca677b6330dacfbd7a3b2e9d0a54dd` |
| `AuthenticatedEarlyC1Projection` | `81a20b8819b3948d81c799e7116892cdc8f266c4941cee4706f3f003f824bce0` | `8da9de08665479d9314cbcbe2ebbdf40bf662b4ed49766abd821775b3eb86704` |
| `AuthenticatedEarlyC1Targets` | `317b2deb64edf2e9991d2ab2e4bb3d22706f6ca1fa4106b72703a5a70ce51432` | `213b36037064f92fe838bdd78cff923a62b5962d51d7e07faba36329ff005336` |

Runner SHA256: `8cf5db4cfe0459425e347a3de4706477a29d4aa5415fc1ae2e94a37514346dc3`.
Representative reused V7 source/olean hashes (the logs contain the full closure):

| Module | Source | Olean |
|---|---|---|
| `V7MerklePrefixTargetCongruence` | `48392fc0677f2423f4cd43e23a9b8ecc337c66afc1c4dcaf40c910c8967a00ed` | `4d22758124c26c67f0c7372c42b657c711d2dac708961772df033348d9496212` |
| `V7MerkleFirstUnresolvedBinding` | `5cc1eb37267545da85f5c33dd51a24c698d89ccf5d2a9c4d9290f3593618ccea` | `ca895c3697720d96c4481bb545bf35083ba35d2a13b685320765929df77dad88` |
| `V7MerklePartialPathExtractor` | `ab5775abb2a01aeaa90db66eca6cad19b47b6114d1b857c203e8c59e4b86090f` | `4ee1845924f4df28e089afeb31993d6fb180ee749ea090d5389647ef7d13a789` |
| `V7MerkleAcceptedOpeningProjection` | `eab66ee9332867390a6cbd31ce9fd8fa23781dc159d95f5757feb7b80eb1df98` | `d8fd15c8024739a3fea07f39aa38feb0712ef72231f333951db7f5cb0537ee24` |
