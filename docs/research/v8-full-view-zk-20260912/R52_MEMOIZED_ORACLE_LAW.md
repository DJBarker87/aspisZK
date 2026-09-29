# R52: exact first-read/memoized oracle law

Base `55f6f65530e6b1dbccd9c4ea23d82268974d45f9` (R51).
Branch `research/v8-r52-memoized-oracle-law-20260929`.

## Result

**44 new Lean theorems and one swap equivalence compile, with 45 axiom
audits.** A finite causal oracle program has exactly the same full-query-trace
and terminal-outcome law under:

1. a uniformly sampled complete oracle on its potential query support; and
2. an interpreter that samples uniformly only at an address's first read,
   stores the answer and replays it at every later read.

This is an exact **interpreter** law, not an assumption that every call is
fresh, a source prover refinement, or an independent-challenge theorem.
Byte-address transcript primitives and an explicit bounded stopping
controller are connected to it. The complete source sampler/prover compiler
and the challenge joint-law bound remain open.

No production/verifier/protocol change, new Rust execution or new SBF run.
Retained CU is **1,620,236 / 1,621,719**; both 1M-cap runs exhaust. Full privacy
and the CU target remain incomplete. Existing negative regressions are intact.

## Exact law, including repeated reads

`Program I A O` has two constructors: return an outcome, or query an address
and choose the continuation from its answer. The program is fixed before
oracle sampling; a continuation can use all previously obtained answers but
cannot consult an unrepresented future oracle answer. The result retains
every query/address-answer pair, including repeats, and the terminal value.

For a fixed partial table `t`, `complete t H` uses stored answers where
present and the complete oracle `H` otherwise. `lazyMean` is the executable
recursive expectation: on a cache hit it takes the stored continuation with
no random draw; on a miss it averages over full answers and installs that
answer in the retained paired-commitment `put` table.

For every rational observation of the query trace and outcome, the proved
identity is

```
mean_H observe(eval(complete(t,H), program))
  = lazyMean(program, t, observe).
```

In particular indicator observations give identical event probabilities.
Nothing is conditioned on acceptance, publication, non-repetition or a good
event. The base case integrates out unused oracle cells, including branches
that stop early. The proof holds for arbitrary fixed cached values; it does
not overwrite them with independent samples.

The only resampling operation in the proof is a **coin-space bijection**:
swap one cell of a complete oracle with an auxiliary uniform answer. This
preserves the uniform measure and justifies the miss branch. It is not a
protocol operation or permission to resample used masks, seed expansions or
cached hash outputs. The hit branch never applies that operation.

## Arbitrary byte addresses without an infinite uniform table

The address type need not be finite. For a finite causal program with finite
answers, define its potential support recursively over **all** answer
branches, not merely the realized trace. Restrict the program to that finite
set, sample a uniform complete oracle there, and extend it arbitrarily outside.

The restriction/renaming proof preserves every query and outcome. The exact
law equals `lazyMean` on the original address type and is independent of the
outside fallback value. This supplies the finite-law meaning for arbitrary
byte-list addresses and full 32-byte answers without positing a uniform
distribution on all infinite byte-list functions.

This potential support is a mathematical construction, not something to
enumerate or send on-chain. Its size is **not** the number of actual oracle
queries and must not be substituted for a runtime/query loss parameter.

## Source and stopping bridges

`SourceOraclePrograms` uses R51's exact source frames and 32-byte state type.
It proves:

- squeeze queries `oldState || 1` then `oldState || 2`, returning the output
  and new state exactly as R51's source-shaped `step` and `calls`;
- absorb queries `state || 0 || label || data`;
- split absorption has the same flattened address;
- a repeated block loop makes exactly `2*n` oracle calls and returns `n`
  output blocks, including repeated-state cases; and
- absorb, squeeze and a causal continuation compose with the exact same
  query trace and state. The general byte-program law applies to this
  composition without expanding its enormous finite support.

The source pins and R51 actual-Rust framing/failure controls remain unchanged
and are checked by the evidence gate. These are source-shaped Lean bridges,
not Rust/Aeneas extraction or a proof that every source hash call is already
represented in the program.

`StoppingOracleProgram` compiles a policy of past query records into a bounded
program. It proves deterministic equality with its direct interpreter,
at most `fuel` calls, no reads after an explicit stop, and the exact oracle
law retaining both stopped and fuel-exhausted outcomes. Real source errors
and public records still need to be encoded in that returned outcome; the
generic type does not do that work automatically.

Small exact controls prove that two reads of one address return the same
answer and reject an independent-per-call transcript with differing answers.
A publication filter returns only `true` values while retaining the rejected
`false` outcome. Its unconditional event law remains exact. Thus this oracle
law does **not** imply uniformity after publication filtering.

## Verification

| Leaf | New theorems | Audits |
|---|---:|---:|
| `OracleResampling` | 6 | 7 |
| `MemoizedProgramLaw` | 9 | 9 |
| `OracleProgramOps` | 4 | 4 |
| `OracleFiniteSupport` | 7 | 7 |
| `SourceOraclePrograms` | 8 | 8 |
| `StoppingOracleProgram` | 4 | 4 |
| `OracleLawControls` | 6 | 6 |

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r52_evidence.py
```

Gate: **29 artifacts, 277 pins, 271 successful cached objects**. New leaves
total **10.52 s** wall time; peak RSS **3,269,492 KiB**. Successful targets:
exit 0, swap 0. Every audited declaration uses no axioms or only `propext`,
`Classical.choice`, `Quot.sound`.

Serial NUC scopes use high/max **3G/5G**, swap max 0, TasksMax 128. Reused the
R51 cache; compiled one missing unchanged table dependency. Failed focused
attempts remain in evidence. One premature dependent launch repeated the
still-failed primitive leaf and is explicitly recorded as a scheduling error.
Inference/finite-support elaboration problems were fixed symbolically, with
no resource, heartbeat, recursion or linter-limit increase. No full replay.

## First remaining source proposition

Compile the **actual bounded sampler algorithms** into these byte programs
and prove that evaluation reproduces their returned values/errors, final
state and entire oracle-call trace. First targets are `challenge_qm31`
(LE words, masking, per-limb rejection/cap, discarded suffix) and the
ordered q22 sampler (draw cap and extra completion-detection block).
Include the nonzero/OOD wrappers without changing their rejection domains.

Then compile the selected whole prover/observer experiment, including all
seed/commitment and transcript calls, grinding, permitted lookahead, retry
policy and publication. Prove its causality; a program chosen using future
oracle answers cannot be passed to this law as a fixed program.

Only after those bridges can the first-read law justify source challenge
accounting. Identifying a sequence of challenge values with independent
uniform field coordinates still requires its own event/selection argument:
cache hits are handled exactly here, not declared improbable or removed.
R50's later-query fixed-root family still has **no proved source
`819/|QM31|` privacy bound**.

Joint H1/G and semantic coverage, the retained Schur target `b - B A^-1 a`,
coherent pre-beta extraction, seed/commitment hops, optimized-word refinement
and complete failure/retry/publication privacy remain release obligations.
No new hiding assumption or global privacy/soundness conclusion is added.
