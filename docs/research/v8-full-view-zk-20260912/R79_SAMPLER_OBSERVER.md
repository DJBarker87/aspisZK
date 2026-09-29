# R79: retained hash-call observations at the actual sampler boundaries

Base revision: `383ff829927ac5a8cf1fc544674ebb16327803b6` (R78).
Branch: `research/v8-r64-guarded-m31-20260929`.

## Why another representation is needed

R78 proves the extracted sampler's complete output/error/state behavior under
the explicit deterministic adapter. The extracted hash callback, however, is
a pure `Input → Result Block`. Equality of outputs cannot distinguish an
extra call, a repeated call or certain reordered calls. Therefore it cannot
justify the retained model's complete oracle trace.

R79 adds a separately named, mechanically instrumented copy of the nine
extracted sampler definitions. `generate_r79_observer.py` checks the exact
R72 source hash and generates only these changes: function-name routing,
the observation monad, the loop operator that threads observation state,
and recording at the two hash call sites. All branches, read operations,
arithmetic, error handling and field functions remain present and in order.
Source-location comments and generated declaration attributes are not copied
onto the separately named observer definitions.
Original Rust, extracted files and earlier proofs are unchanged.

This checker is **not a formally certified compiler**. Its literal-source
instrumentation check is a visible trust boundary. The instrumented copy is
not silently relabelled as the original extraction, and compiling it does
not establish the complete source-observer theorem.

## Exact compiled/proved boundary

Five Lean leaves compile. `SamplerObservedSource` contains the nine
instrumented definitions; the other four leaves have 17 audited theorems.

- `SamplerObservation` defines successful-call records containing the exact
  segmented input and returned block, with append-only observation state.
- `SamplerObservedLaws` proves the monadic execution equations and an exact
  unfolding equation for the existing Aeneas loop with observation state.
- `SamplerObservedSqueeze.execution` proves the instrumented generated
  squeeze makes the two hash calls in the source order and appends their
  input/output records. Both frames use the **old** state, with tags 1 and 2.
- `SamplerObservedSqueeze.erase` proves erasing that observation state
  recovers the original extracted squeeze, for arbitrary hash callbacks,
  including backend failure and divergence.
- Under the explicit total adapter, `decoded_execution` proves the observed
  bytes and answers equal the retained `SourceDuplexStep.calls`, together
  with the same output block and next state. Existing history is retained.
- `SamplerObservedInnerStep` proves exact factoring of the instrumented
  inner-loop body. Exhaustion and existing-block reads add no events.
  Rollover delegates to the observed squeeze and otherwise preserves its
  record, while retaining the actual word decoding and rejection predicate.

The observer uses `StateT Trace Result`: a backend failure/divergence does
not return a successful trace or preserve a separately visible prefix in
its return value. Sampler exhaustion variants are ordinary values inside
`Result.ok`, so they retain observation state. No claim about backend-failure
prefix traces is made. The target adapter is total, but full instrumented
sampler totality/correspondence still needs the following composition.

## First remaining proposition

Prove the **instrumented** eight-attempt rejection loop's full trace equals
the retained per-limb oracle program, then the four-limb mutable write-back
and the three-attempt circle wrapper, with exact errors and advanced state.
Establish complete observer/source correspondence with the instrumentation
trust boundary explicit. Squeeze erasure and one-step observations alone
do not prove that complete theorem.

After that, instantiate the retained coherent memoized-oracle laws in the
actual transcript experiment. Prior-query history, reused addresses, seed
expansion, joint commitments, later messages, retries and publication are
not justified merely by these observation lemmas. No new hiding assumption,
fresh independent-answer premise, concrete SHA ideality or privacy advantage
bound has been introduced. Full privacy and full soundness remain open.

## Verification evidence

Lean `leanprover/lean4:v4.32.0`, `lake env lean -j1 -M4500`, existing NUC
cache. Actual cgroup: MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0,
TasksMax 128. Focused compilation preceded one final five-target replay,
reusing 339 targets and verifying 297 dependency pins. No dependency rebuild.

All target names below have prefix `AspisV8R19/`.

| Exact target | Exit | Wall seconds | Peak RSS KiB | Job swaps |
|---|---:|---:|---:|---:|
| `SamplerObservation` | 0 | 2.07 | 3,689,536 | 0 |
| `SamplerObservedSource` | 0 | 2.13 | 3,695,576 | 0 |
| `SamplerObservedLaws` | 0 | 1.92 | 3,690,528 | 0 |
| `SamplerObservedSqueeze` | 0 | 3.01 | 3,704,944 | 0 |
| `SamplerObservedInnerStep` | 0 | 5.70 | 3,719,624 | 0 |

Thirteen theorem audits use standard Lean axioms only. Four inner-step
audits retain the known opaque `core.fmt.Formatter : Type` through the
generated unwrap signature. No new axioms or admitted proofs. Final logs
have no warnings, errors or `sorryAx`; the release remains **PASS_SCOPED**.
The evidence retains failed focused attempts: state-monad application
normalization, unfolding beneath a matched pair, and branch normalization
in the factored inner body. These were fixed locally without larger caps.

Recheck the retained evidence without recompiling:

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/check_r79_evidence.py
```

No runtime/protocol change, new SBF measurement, deployment or wallet action.
Retained complete CU: **1,495,663 / 1,497,050**; both actual 1M runs exhaust.
