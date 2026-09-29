# R66: checked optimized CM31 kernels and generated QM31 try-inverse

Base revision: `b6033bddee22638b7f0f86a2e25cdd838c53c787`.
Date: 2026-09-29. Runtime, protocol and proof bytes unchanged.

## Exact proved boundary

The selected implementation's **actual QM31 `try_inv` closure** now has a
compiled generated-execution theorem for every canonical four-word input:

- all-zero input returns `Result.ok none`;
- every nonzero input returns `Result.ok (some inverse)`, with all four output
  words canonical and decoding to the exact QM31 field inverse;
- no canonical input produces an internal `Result.fail`, including the base
  inverse assertion failure;
- decoding the returned option agrees with R60's retained
  `NormInverse.tryInverse` model.

The theorems instantiate the actual norm and inverse code. Nonvanishing of the
norm follows from the retained exact field tower; it is not an added premise.
There is no injected inverse/hiding/nonsquare assumption. This is universal
canonical-word execution, not a finite test or a standalone algebra identity.

Endpoints in `QuarticInverseExecution.lean` are `try_inverse_execution`,
`none_iff_zero`, `some_inverse`, `no_failure`, `entry_execution`, and
`retained_model_correspondence`.

## Optimized kernels retained

The proof does not replace CM31 multiplication or squaring with generic field
operations before proving execution. It covers the selected source's widened
raw sums, the `r23_product_u32_bounded` fast path, narrowing/widening casts,
checked additions/subtractions/products and full canonical reduction.

For canonical inputs, the raw sum and difference factors are below `2^32`;
their product fits `u64`. Those bounds prove that the source takes its guarded
fast path without overflow or truncation. The field identities are applied
only after proving the word execution. No claim is made here about the
out-of-range fallback of the width helper: the proved callers establish its
fast-path conditions.

The four compiled leaves are:

1. `QuarticFieldSlice.lean`: exact bodies for 28 generated declarations
   (three types, one global, 24 functions). Import framing includes the cached
   full-runtime `CoreConvertNum` module; generated declarations are unchanged.
2. `QuarticBaseExecution.lean`: 20 theorems, transporting R65/R64 M31 results
   and proving subtraction, reduction, width conversion/product and zero test.
3. `LazyComplexExecution.lean`: 11 theorems for raw operand bounds and actual
   CM31 sub/neg/mul/square/mul-by-R/inverse/zero-test execution.
4. `QuarticInverseExecution.lean`: 13 theorems for representation, the exact
   `Option` and failure behavior, inverse correctness and retained-model equality.

## Source lock and extraction

The dependency-free wrapper calls `x.try_inv()`. Fresh Charon/Aeneas extraction
copies four field source files unchanged from the selected R62 stage and checks
all 197 stage pins. It uses release Rust, offline/locked dependencies and
explicit overflow checks matching the retained SBF environment. The closure has
24 local nonopaque functions and no extra trait declarations/implementations.

Artifact pins:

- LLBC: `b1fdd1f9669fd9b8236eb263d96da0facd6da48016707fe1ab84733912fe26d2`
- Functions: `74b0f6ca419ac7cb147e539b849ff0a31006d00be950f0b83b312fda12b4622a`
- Types: `2433db0496ad548f2a1ffd2bd632c842daed6086f6656d7bb9959fbefdd7c6ad`

The audit checks every extraction pin and exact complete declaration bodies,
and rejects twelve negative mutations, including wrong norm operands, width
casts, subtraction, zero-test component, and mul-by-R input.

The trust boundary remains **pinned generated execution under the Aeneas
runtime/extraction model**, not a verified Rust compiler or SBF instruction
theorem. Canonicality is an explicit representation condition, not a waiver of
untrusted-byte checks. `Result`/`Option` correspondence is not by itself a
theorem about every external log, failure or publication observer.

## Executed evidence

Final cache: `/home/dombarker/project-offloads/aspis-r66-final-20260929-a`.
Lean 4.32.0, `lake env lean -j1 -M4500`; 306 cached targets reused, 310 final.
No cold dependency build or package-wide replay. After focused predecessors
passed, one final four-leaf replay ran.

| Target | Exit | Wall seconds | Peak RSS KiB | Swaps | Axioms audits |
|---|---:|---:|---:|---:|---:|
| Checked extraction | 0 | 0.99 | 219632 | 0 | — |
| Translation | 0 | 0.37 | 71456 | 0 | — |
| QuarticFieldSlice | 0 | 1.99 | 2528964 | 0 | 0 |
| QuarticBaseExecution | 0 | 2.48 | 3694036 | 0 | 20 |
| LazyComplexExecution | 0 | 2.67 | 3698696 | 0 | 11 |
| QuarticInverseExecution | 0 | 2.06 | 3689176 | 0 | 13 |

All 44 audits report only `propext`, `Classical.choice`, `Quot.sound`, or a
subset. No `sorryAx` or new axioms. Actual cgroup settings were recorded:
MemoryHigh=5 GiB, MemoryMax=7 GiB, MemorySwapMax=0, TasksMax=128. Jobs ran
sequentially. There are 212 transitive source/runtime-object pins.

Two failed development checks are retained: the declaration slice initially
needed the cached conversion-module import, and the product-bound proof needed
an explicit intermediate inequality to avoid elaboration choosing the wrong
factorization of `2^64`. Neither was a resource failure or protocol failure.

The read-only evidence checker passes with 31 artifacts and 323 source pins:

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r66_execution.py
```

## First remaining source proposition

Prove the **complete `secure_ood_circle_point_from_parameter` execution** against
the retained circle model, preserving singularity-before-subfield error order.
Its next arithmetic prerequisite is the current **guarded QM31 multiplication**
path (`r24_canonical_mul`, with its bounded wrapping expressions and partial
reductions), plus outer QM31 square/add/sub and CM31 equality. Do not replace
that path with the fallback Karatsuba formula and call it the current source.
The QM31 multiplication path is not used by `try_inv` itself and is therefore
not covered by this milestone.

The inspected local circle/transcript files match the selected stage:
`circle.rs` SHA-256 `8f6f0f32c8dd93e3ee459df0c1d0ef710b01996d3bc929dbeffb3f7d14a0227c`;
`transcript.rs` SHA-256 `be036d144b9fe0c8119d9f6fdd8ca2167d1379f7d1d785fa2f197200b9f7d119`.
After the circle map, connect bounded sampler control flow, decoding, shared
oracle interaction and its failure observer. The existing mathematical sampler
law is not yet a universal theorem about that entire source path.

Full commitments/seed expansion/shared-oracle/semantic/OOD/final/opening views,
visible failures/retries/publication and justified numerical loss bounds remain
open. Coherent pre-beta quotient-pair extraction remains a separate soundness
obligation. The retained C1 failure and fixed-block results remain distinct.

No runtime change, no new SBF run, no production path change. Retained complete
primary CU is **1,497,377 / 1,498,764**; both actual 1M runs still exhaust.
Full privacy and full soundness are not established.
