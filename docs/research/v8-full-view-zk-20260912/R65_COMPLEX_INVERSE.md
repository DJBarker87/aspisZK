# R65: generated CM31 inverse execution

Base revision: `70b2494f91a4dae94059f96900232dac5a611ccc`.
Date: 2026-09-29. Runtime/protocol unchanged.

## Exact result

The selected source's **actual CM31 inverse**, with its actual M31 inverse
backend, now has a compiled generated-execution theorem on every canonical
pair of M31 words. It terminates and returns the canonical exact-field inverse
for every nonzero pair; its `Result` is assertion failure **if and only if both
input limbs are zero**. No injected-backend correctness premise remains in the
final theorem. The existing exact-tower norm theorem supplies nonvanishing;
there is no new nonsquare, hiding or cryptographic assumption.

Three focused leaves compile with 25 theorem/axioms audits:

- `ComplexFieldSlice.lean`: all 14 generated declarations (two types, one
  global and eleven functions), with exact bodies and narrowed import framing.
- `ComplexBaseExecution.lean`: 15 theorems. It transports the checked M31
  reducer/multiplication/loop/inverse results from R64, proves checked canonical
  addition and negation, and connects word encodings to the exact base field.
- `ComplexInverseExecution.lean`: 10 theorems. It proves encoding round trips,
  canonical output, nonzero inverse correctness, exact zero failure and the
  complete canonical-input execution split, including the extraction entry.

The endpoint is `ComplexInverseExecution.inverse_execution` and its source-entry
corollary `entry_execution`; `inverse_failure_iff` identifies zero by raw limbs.
These are universal theorems on canonical words, not finite field tests.

## Source and extraction boundary

Fresh Charon/Aeneas extraction starts from the dependency-free
`complex_inverse_probe`, which calls `x.inv()`. The four selected field source
files are copied unchanged from `aspis-r20-r62-gather-20260929-b`; all 197 stage
pins are checked. The source is the measured R62 implementation, not an older
generic arithmetic template. The release profile explicitly enables overflow
checks, matching the selected SBF environment and retaining the R64 correction.

The source audit checks the eleven extraction artifact pins, hard-pinned LLBC,
generated types/functions and translation metadata, and exact complete
declaration bodies. All eleven generated functions are local and nonopaque.
Eight negative mutations of addition, zero test, negation, norm, backend input
and actual inverse selection are rejected. An injected function argument exists
in generated `inv_with`, but final `CM31.inv` instantiates `M31.inv` and its
proved source-execution chain, not a hypothesized inverse.

Pins:

- LLBC: `0106be4ac9bac6f09319a84bd4860de01773cce9c89beeb34812f9626dd6c533`
- Generated functions: `13cef0ccd8b41a55910ddb6c09691c2aececd0008756764f5878f7062cc8c9d9`
- Generated types: `94db6c53943ea6a2f8597b3508b096fbc123984b816a549c75aa5fd17726b8ff`

This is source-pinned execution **under the retained extraction/runtime model**.
It is not a verified compiler/SBF-machine theorem. Canonical inputs are an
explicit representation condition; this result does not assert that arbitrary
untrusted bytes have already satisfied it. The failure result is an Aeneas
`Result` equality, not a theorem about all panic text, logs or publication.

## Executed evidence

NUC final cache: `/home/dombarker/project-offloads/aspis-r65-final-20260929-a`.
Reused 303 cached targets; final metadata has 306. Lean 4.32.0, sequential
`lake env lean -j1 -M4500`, no dependency rebuild.

| Target | Exit | Wall seconds | Peak RSS KiB | Swaps | Axioms audited |
|---|---:|---:|---:|---:|---:|
| Checked extraction | 0 | 1.02 | 219272 | 0 | — |
| Translation | 0 | 0.35 | 69168 | 0 | — |
| ComplexFieldSlice | 0 | 1.33 | 2516280 | 0 | 0 |
| ComplexBaseExecution | 0 | 1.97 | 3685940 | 0 | 15 |
| ComplexInverseExecution | 0 | 1.72 | 3678028 | 0 | 10 |

All audits use only `propext`, `Classical.choice`, `Quot.sound` (or a subset).
No `sorryAx` or new axioms. The final run records actual kernel cgroup settings:
MemoryHigh=5 GiB, MemoryMax=7 GiB, MemorySwapMax=0, TasksMax=128. Jobs were
sequential. The runner pins 168 transitive local/runtime sources and used
runtime objects. No package-wide or unchanged runtime regression was run.

Two base-leaf development failures and one composition-leaf failure are retained
with their source hashes and exit-1 logs. They were local proof notation/rewrite
errors, not failed mathematical propositions or memory-pressure kills. The
runner reuses successful predecessor outputs while excluding failed targets;
after focused success it performed one final three-leaf replay.

Audit command:

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r65_execution.py
```

Evidence: `evidence/r65-complex-inverse/`, including extraction, logs, source
audit, dependency/source pins, failed-development logs, receipt and manifest.

## First remaining proposition

The actual **QM31 `try_inv` execution** remains unproved. Its source first uses
optimized CM31 `square`, `sub`, `mul_by_r`, then the now-proved CM31 inverse,
followed by optimized CM31 multiplication and negation. The next prerequisite
is universal canonical-word execution of those CM31 arithmetic operations,
including the checked `r23_product_u32_bounded` path and reducer, followed by
the source zero test and `Option`-returning QM31 composition. Do not substitute
the generic complex multiply for the current lazy/raw-representative code.

Then the circle map and bounded sampler must be connected to source execution
and the observer. Full shared-oracle/seed/commitment laws, all semantic/OOD/
final/opening disclosures, visible failures/retries/publication and justified
numerical loss bounds remain open. Coherent pre-beta quotient-pair extraction
is a separate soundness obligation. This result does not close any of those
global gates or erase the retained C1 negative regression.

No runtime, production protocol or proof wire changes; no new SBF benchmark.
The retained complete-primary CU is **1,497,377 / 1,498,764**. Both actual 1M
executions still exhaust. Full privacy and full soundness remain unestablished.
