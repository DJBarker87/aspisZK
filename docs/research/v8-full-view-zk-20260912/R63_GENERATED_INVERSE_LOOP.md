# R63: generated inverse-loop execution

Base `491ccd3d42e2e07ff2c04cb6dd17c7ea20269ed0` (R62), branch
`research/v8-r63-generated-inverse-loop-20260929`. Proof/evidence only; no
protocol, runtime, production, wallet, deployment or settlement change.

## What is proved

Three focused Lean leaves compile against Lean 4.32 and the **full cached
Aeneas runtime**. They do not import R17's projected scalar representation.

- `InverseFieldSlice.lean` retains eight byte-identical declarations from
  the pinned generated Types/FunsChunk04: M31, P, reducer, multiplication,
  square-loop body, square loop, square wrapper and guarded inverse.
- `InverseRuntimeMul.lean` replays 21 retained reducer/support arguments
  against actual runtime operations. For every pair of U32 inputs, the
  generated multiplication succeeds with their canonical product modulo P.
- `GeneratedInverseLoop.lean` proves nine bridge theorems. The actual
  `IteratorRange.next StepUsize` follows its bounds; induction on remaining
  range length proves generated `square_n_loop` termination and output.
  This covers every representable count, not only the constants 2/4/8.
  Generated `M31.inv` on a canonical zero returns `assertionFailure`; on a
  canonical nonzero word it succeeds with R60's word chain. The decoded
  canonical result equals the field inverse.

The loop theorem uses the runtime's partial-fixpoint equation. It does not
replace the generated loop by an assumed terminating Nat recursion, enumerate
field inputs, or normalize a giant concrete recurrence. R60 supplies the
symbolic chain/inverse algebra. All **30** theorem axioms reports contain only
`propext`, `Classical.choice`, and/or `Quot.sound`; no `sorryAx`, new axiom,
assumed inverse primitive or hiding assumption is used.

## Important source boundary caught by the audit

The selected R62 SBF stage **does not use exactly the extracted M31 multiply**.
It has the earlier guarded one-fold optimization:

```
canonical operands -> one Mersenne fold and conditional subtraction
otherwise          -> original two-fold reducer
```

The retained generated declaration uses the original two-fold reducer
unconditionally. The inverse schedule and square-loop Rust bodies agree, but
that does not establish operational equivalence of the changed multiply.
The first release preflight stopped on this mismatch before compilation.
The audit now authenticates both the unchanged generated declarations and the
exact selected optimized source, and explicitly records the unproved bridge.
No generated-source pin was relaxed or replaced.

**First remaining proposition:** for the selected guarded M31 multiply,
establish checked-word execution equivalence to the generated multiplication
(including bounds, narrowing, canonical output and fallback), and transport
the loop/inverse execution result across it. Then compose actual word-level
CM31/QM31 norm, negation, equality, `try_inv`, and circle-sampler execution.
The older arithmetic tests and formulas are useful inputs, not that universal
execution proposition.

Even the proved generated leaf is under the retained Aeneas runtime/extraction
model. Byte matching and Rust structural checks are **not a verified Rust
compiler theorem**. This milestone is not universal refinement of the whole
current field tower or sampler.

## Exact compilation evidence

| Focused target | Exit | Wall | Peak RSS (KiB) | Axioms reports |
|---|---:|---:|---:|---:|
| InverseFieldSlice | 0 | 1.17s | 2,505,792 | 0 (definitions) |
| InverseRuntimeMul | 0 | 1.34s | 2,512,148 | 21 |
| GeneratedInverseLoop | 0 | 1.98s | 3,678,384 | 9 |

All reported swaps are zero. Final replay uses `lake env lean -j1 -M4500`,
one target at a time, in the retained cached workspace. It reuses 296 prior
targets and produces a 299-target cache. No cold dependency build, package-wide
Lean replay, unchanged Rust suite or SBF rebuild was run.

NUC scope: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128;
maximum simultaneous reservation 7 GiB. Preliminary focused development
errors were import/namespace, bound inference, and rewrite-shape errors;
none was a memory kill and the cap was not increased. Final evidence retains
the three loop-development failure logs and the import probe, plus an explicit
record of earlier preflight corrections.

The source audit verifies 197 selected-stage pins before the final compile,
the two fixed generated-file hashes, eight exact declaration bodies, eight
negative generated mutations, the R60 nine-binding/38-multiplication schedule
and its five negative controls. It records 137 transitively visited local/
runtime source and runtime-object pins. Exact source hashes, base revision,
commands and resources are retained alongside the logs.

Reproduce in a fresh output directory on the cached NUC:

```
tools/run_r63_lean.py --output /absolute/fresh/output
```

Invoke inside the stated capped systemd scope. Successful cache:
`/home/dombarker/project-offloads/aspis-r63-lean-20260929-b`.

Local read-only evidence audit:

```
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r63_evidence.py
```

## Full-goal and CU status

Full privacy remains open: optimized/current field and sampler correspondence,
shared-oracle and seed/commitment behavior, all observer disclosures, causal
transcript simulation, failures/retries/publication and justified quantitative
losses still need composition. Coherent pre-beta quotient-pair extraction is
a separate soundness obligation. C1 negative regressions, fixed-block hiding
and joint coverage remain distinct; none is promoted to global privacy here.

R62 remains the selected runtime: **1,497,377 / 1,498,764 CU**. Both actual
1M-cap runs exhaust. No new runtime measurement or CU saving is claimed.
