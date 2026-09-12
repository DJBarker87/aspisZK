# Cached-oracle execution and constructed early commitment cuts

This slice constructs a source-shaped early transcript with a shared cached
oracle. It does **not** establish global Fiat–Shamir soundness, the complete
selected verifier's source refinement, or a checked payment extractor.

Base inspected: `9e65594156c06b53a2ebea2041a9662850d6bbb8`.
Sources inspected: `crates/aspis-core/src/transcript.rs` (`absorb`,
`squeeze_block`, `challenge_qm31`, nonzero/OOD/query samplers), and
`experiments/performance_verifier.rs::semantic` in the earlier research folder.

## What is now constructed

`FSOracleExecution` implements one chronological full-answer cache/log.
Every requested hash input emits an event, including cache hits. Only a cache
miss consumes a tape entry. Returned answers are installed and existing answers
are preserved across all subsequent causal script execution. Scripts explicitly
return a value or abort and have an upper bound on calls. Their response
continuations receive only the current answer, not future tape entries.

`run_extends`, `run_preserves_answer`, `retained_prefix`, `call_bound`, and
`run_tape_congr` are proved from that interpreter. `queryHash_refines` separately
proves deterministic agreement with a fixed hash function given a consistent
starting cache. It is not a random-oracle distribution theorem.

`FSBoundedTranscript` uses those calls to implement:

| Source operation | Literal interpreted bytes/control |
|---|---|
| absorb | old state, byte 0, actual label, data |
| squeeze output | old state, byte 1 |
| squeeze advance | old state, byte 2 (not the output answer) |
| QM31 sampling | four little-endian 31-bit limbs; reject exactly p; eight tries per limb; shared eight-word block stream |
| C1 root absorption | label 3, 26 bytes |
| C2 root absorption | label 9, 26 bytes |

The selected `semantic` order is C1, lambda, chi, C2. `earlyWithC2`
constructs that prefix, including an adaptive bounded C2-building hash script
after the two challenges. Its leaf/internal/adversary-first calls share the
same log/cache. The C2 cut is **after construction and before root absorption**.
It is not merely the time immediately after chi. The higher-level
`constructBoth` also executes the C1-building bounded script before that
sequence: neither root is caller-supplied at this endpoint. `constructed_cuts`
produces initial-history → post-C1-builder/pre-C1-absorption →
post-C2-builder/pre-C2-absorption → final-log nesting. Pre-existing adversary
queries remain in the initial environment. Profile, statement and optional
positive-transfer framing precede this slice and are not reconstructed here.

`early_script_cuts` and `early_script_take` construct and prove chronological
nesting and literal take equalities for both cuts. There is no root-equality-only
premise and no supplied answer-log membership. `early_script_abort_prefix`
keeps the actual log after failed samplers or an aborting C2 builder.
`c2_builder_continuation_congr` proves the builder uniformly respects a shared
post-chi history across tapes agreeing on at most its next n fresh entries.

The older `early` helper is explicitly a no-hash C2-choice control, not the
general adversary. General cut claims should use `earlyWithC2`.

## Premises and remaining producers

- Initial transcript/cache/log: raw environment; initial cache/log consistency
  and source-derived profile/statement framing are still needed for an
  end-to-end instantiation.
- Tape: all full 256-bit answers. No independent law is postulated or proved.
  To obtain lazy-ROM probability, the adversary/program must be chosen before
  unseen tape entries and each newly consumed answer must have the appropriate
  conditional law. A source state collision can cause cache reuse.
- C1/C2 producers: explicit legal bounded hash scripts chosen from the available
  history/challenges. Their actual returned roots determine the later absorption
  inputs. Real adversary-to-script operational refinement, including hash calls
  performed by a concrete commitment builder, remains to be supplied.
- Success in `early_script_cuts`: a result of this independently defined early
  interpreter, not a renamed ideal acceptance or a terminal-equation premise.
- Limbs: represented as natural numbers with source-shaped masking. Conversion
  to the concrete QM31 structures and machine-word byte decoding needs a literal
  Rust refinement, not just the present source correspondence inspection.
- Subsequent nonzero/OOD/distinct query samplers and all semantic/relation
  messages: not implemented in this slice. No complete Aspis strategy claimed.
- Authentication collision/late-target events: existing definitions have not
  been replaced. These newly constructed cuts still need connecting to those
  exact definitions and to the authentic shared hash log.

## Executed checks

Small leaf commands in the local pinned Lean folder:

```
lake env lean -j1 -M2048 -o /tmp/FSOracleExecution.olean FSOracleExecution.lean
LEAN_PATH=/tmp lake env lean -j1 -M2048 FSBoundedTranscript.lean
```

Use a fresh unique build directory instead of `/tmp` in the retained integrated
runner. The only first-party imported artifact is freshly compiled
`FSOracleExecution`; Std comes from the pinned toolchain distribution.
Lean version: 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
Both final focused compilations exit 0. Final timed checks: oracle leaf
0.56s/696,156,160-byte peak RSS, bounded transcript leaf
1.16s/681,885,696-byte peak RSS; both zero swaps. These are developer check
measurements, not release certification; use integrated durable logs/hashes.
Printed axiom lists contain only `propext` and `Quot.sound`.

The Lean executable controls establish:

- Constant-zero oracle: canonical lambda/chi both succeed, six logged calls
  but four fresh answers, with flags `[true,true,true,false,false,true]`.
  Cache hits are not treated as new independent challenges.
- All-255 oracle: first-limb exhaustion aborts after three calls, no C2 root.
- One C2-builder hash call moves the C2 cut from five to six calls and final
  log length from six to seven. An aborting builder retains that sixth call.
- Both builders invoked: C1 cut one, C2 cut seven, final eight total calls with
  six fresh answers. Root construction is no longer omitted at either cut.

During local proof development, a conflicting pair of simp rewrite rules,
documentation comments before `#guard`, a reserved identifier, and an
insufficiently unfolded cache-consistency predicate failed compilation and
were repaired by local decomposition; no theorem statement was weakened.
No unchanged broad build, kernel replay or historical artifact substitution ran.

## What a global resource ledger still requires

Let Q count distinct full hash inputs and let each chronological commitment
cut supply its actual unresolved target set. Under a proved fresh-answer ROM
coupling, truncated-output collision union accounting has the familiar
`choose(Q,2)/2^208` form. A late-target term requires actual fixed target
cardinalities and eligible post-cut fresh calls; no number is assigned here.
Repeated calls still cost time but are not independent hazard trials.

Do not multiply the old conditional approximately 103.999872-bit residual by
an invented compiler round count. Conversely, it cannot become a
resource-independent 100-bit FS probability. Even a legitimately justified
per-attempt union at that residual scale has only room for 15 trials before
other errors under a `2^-100` target. This is a diagnostic about a hypothetical
union, not an actual Aspis retry theorem or an imposed adversary limit.
Resources for prequeries, retries, forks/restorations, sampler aborts, target
selection and witness extraction remain explicit unknowns. Grinding credit is
zero. No global probability, adaptive ZK or CU claim is made by this slice.

**Next producer:** connect actual pre-C1 transcript construction and the
same-body semantic interpreter to this cached execution, then extend the
source samplers/messages while preserving the uniform program across histories.
