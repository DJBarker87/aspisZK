# R80: complete instrumented QM31 challenge trace

Base revision: `8b4d9f417497961530e818419156ae5968c7ef31` (R79).
Branch: `research/v8-r64-guarded-m31-20260929`.

## Exact result

Six Lean leaves compile with 19 theorem audits. For the explicit total
deterministic hash adapter and arbitrary hash function H, the instrumented
QM31 challenge agrees with the retained oracle program on the complete
ordered query/answer history, sampled result or exhaustion error, and next
state. Erasing the observer returns the original extracted QM31 challenge's
result and state. No Rust, original extraction, protocol or instrumentation
definition changed.

- `SamplerObservedInnerLoop`: exact observed eight-attempt rejection loop,
  with shared cursor and backend result behavior preserved.
- `SamplerObservedLimbBridge`: raw observation witnesses and decoded trace
  correspondence for reads and limb rejection; per-limb erasure under the
  explicit adapter. Trace equality is proved, not inferred from output equality.
- `SamplerObservedLimbLoop`: instrumented mutable iterator and four-limb
  entry, retaining the actual deferred stores and original finish operation.
- `SamplerObservedWriteback`: four-limb model correspondence, including
  early exhaustion, advanced state and observations. On early exhaustion the
  unused partial internal array is existential, not claimed equal to an
  externally visible value.
- `SamplerObservedChallenge`: complete challenge trace, mandatory initial
  squeeze, reconstruction and erasure to the original extracted challenge.
- `SamplerObservedProgram.oracle_program`: the decoded public view equals
  `MemoizedProgramLaw.eval H (QM31SamplerProgram.challengeProgram s)`.
  The internal hash-function pointer is excluded from the observable view.

This is an exact interpreter correspondence, **not full privacy**. R79's
literal-source instrumentation checker remains an explicit, non-certified
trust boundary. The observer is `StateT Trace Result`; backend failure or
divergence does not return a separately retained prefix trace. Sampler
exhaustion is an ordinary returned variant and its history is retained.
The complete challenge theorem uses the stated total adapter, not arbitrary
failing backends and not independent fresh answers.

## First remaining proposition

Compose the instrumented secure-circle outer retries with this QM31 observer
and the proved exact circle map, preserving ordered observations, both
exhaustion errors and advanced state. Then connect the complete source
observer to the actual coherent-oracle experiment. Prior queries, repeated
addresses, seed expansion, joint commitments, later messages, retries and
publication still require their justified source premises. No concrete SHA
ideality, new hiding assumption or global privacy/soundness bound is claimed.

## Verification evidence

Lean `leanprover/lean4:v4.32.0`, `lake env lean -j1 -M4500`, cached NUC
workspace; MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0, TasksMax 128.
Focused targets preceded one final six-target replay, reusing 344 targets
and checking 318 transitive dependency pins. No dependency rebuild.

All targets have prefix `AspisV8R19/` and extension `.lean`.

| Exact target | Exit | Wall seconds | Peak RSS KiB | Job swaps |
|---|---:|---:|---:|---:|
| `SamplerObservedInnerLoop` | 0 | 2.23 | 3,704,436 | 0 |
| `SamplerObservedLimbBridge` | 0 | 2.02 | 3,703,100 | 0 |
| `SamplerObservedLimbLoop` | 0 | 2.69 | 3,717,224 | 0 |
| `SamplerObservedWriteback` | 0 | 1.91 | 3,707,928 | 0 |
| `SamplerObservedChallenge` | 0 | 1.85 | 3,706,472 | 0 |
| `SamplerObservedProgram` | 0 | 1.72 | 3,707,988 | 0 |

Three theorem audits use standard Lean axioms only; 16 retain the previously
documented opaque `core.fmt.Formatter : Type` through generated unwrap
signatures. No new axioms, admissions, final warnings or `sorryAx`.
The result is **PASS_SCOPED**, with 79 hashed evidence artifacts.

Failed focused attempts are retained: StateT normalization and rewrite
transparency, an invalid selective-open syntax, prematurely unfolding a
cursor before applying the per-limb equality, and a program-view rewrite.
One write-back launch preceded confirmation of its prerequisite and failed
in 0.13 seconds on a missing `.olean`; it was retried only after the
prerequisite compiled. A redundant simp warning was removed before the final
replay. No cap increases or unchanged full regression reruns were needed.

Recheck retained evidence without compiling:

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/check_r80_evidence.py
```

Runtime/CU unchanged: **1,495,663 / 1,497,050** complete executions; both
actual 1M-cap runs exhaust. No new SBF measurement, deployment or wallet work.
