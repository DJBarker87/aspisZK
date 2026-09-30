# R99–R100: folded opening inverses and observed q22 execution

2026-09-30; base `059abfb388290177bbb1857745fc48e3ae9e3833`.
Research only; neither under-1M execution nor full security is achieved.

| Complete verifier | World 0 CU | World 1 CU | Decision |
|---|---:|---:|---|
| Pushed R98 control | 1,125,129 | 1,123,391 | Retain |
| R99 generic folded inverse | 1,125,817 | 1,124,003 | Reject regression |
| R99 private canonical folded inverse | **1,123,090** | **1,121,361** | Compose research winner |

The same two R84 proof hashes remain pinned. Both actual 1M honest executions
still exhaust; **123,090 CU remains**. All corrupted combined finals reject
with Custom(6), without resource failure, at both caps. Heap is 262,144 bytes;
simulated accounts are unchanged. This is not settlement or a universal CU bound.

## Exact-output opening experiment

For signs `(sx,sy)` in the actual slot order `(++,+−,−−,−+)`, the chord is
`D=A+sx Bx+sy Cy`. The normalized circle-fold coefficient is
`b=(x+sx alpha²)(y+sy alpha)/(4xy)`. The new path expands `b conjugate(D)` into
four sign-parity coefficients, using the source-selected unit-circle identity
`x²+y²=1`. It multiplies these by the existing CM31 norm inverses, then takes
one four-term dot against the same quotient numerators. This replaces separate
quotient products followed by the three-product fold; no new public hint or
probabilistic check is introduced.

The generic implementation passes equality but loses 688 / 612 CU. Keeping
the coefficient work in the existing private canonical representation wins
2,039 / 2,030 CU versus the control. The complete measured reduction is modest;
the lower product count is not itself a CU claim.

The internal contract is the SAME source-derived points, chord values and line
coordinates. The old arbitrary quotient kernel remains unchanged. Every
denominator/domain check, full packed canonical decoding and authenticated
byte sequence remains. Batch failure still falls back per record in the same
error order. Crucially, fallback recomputes ordinary inverses; it never mistakes
the folded weights for ordinary inverses. No parser, query count, digest width,
challenge or proof-profile change is selected.

Executed gates: 4,096 chord profiles, **174,288 weight comparisons and 87,144
complete folds**, including alpha zero/one, 306 zero-chord profiles and 132
malformed kernel-boundary controls. The frozen quotient/packed-source checks,
both genuine host audits, 3,282 wire cases (3,281 checked rejections), SBF stack
and frozen-table gates and complete runtime all pass. An earlier staging-anchor
failure produced no manifest or compiled artifact and is recorded separately.

The selected ELF is
`91de5b67d15e9c938916b0693e5e59b881cad7ec8c9bcd9c31c63253d4a1c310`.
Its exact world-0 trace matches clean CU and ELF text: 1,013,018 executed
instructions, 65,009 integer multiplies, 195,622 loads and 122,344 stores.
These are exclusive instruction counts, not inclusive region CU budgets.
Inherited trace-driver scope labels do not replace the clean full-runtime gate.

## Complete selected q22 observations

`generate_r100_query_observer.py` mechanically instruments five declarations
from the pinned R98 Aeneas extraction. Only the monad, local call names, loop
operator and two hash-observation sites change. The hash-free inner scan is
the actual extracted computation lifted unchanged. This generator is checked
byte-for-byte, but it is **not** a certified instrumentation compiler.

The proofs cover each actual squeeze, the actual outer loop and public guard,
the ordered input/output hash history, the exact typed sampler result and final
state, and erasure back to the retained source. They include completion
detection, duplicates, retries and draw exhaustion; no artificial cutoff outcome
is added. The same total deterministic hash adapter is reused throughout.

The public-view theorem is then linked to the finite oracle program and its
memoized ideal-oracle law with arbitrary prior cached answers. Used answers
are retained, not resampled. This closes the **selected q22 sampler** observer
boundary, not the entire protocol's shared-oracle experiment.

| Final focused Lean target | Exit | Wall | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| `QueryObservedSource` | 0 | 2.31 s | 3,676,816 | 0 |
| `QueryObservedBlock` | 0 | 3.40 s | 3,694,572 | 0 |
| `QueryObservedExecution` | 0 | 3.10 s | 3,698,152 | 0 |
| `QueryObservedProgram` | 0 | 2.44 s | 3,684,816 | 0 |

Lean 4.32.0 reuses 364 compiled predecessors with 319 transitive pins. Each
changed file is checked first, then one final four-leaf replay. Failed local
elaboration and an unused-simp warning are retained with their corrected runs.
The final replay has no warnings or admissions. Twelve `#print axioms` audits
use propext, Classical.choice and Quot.sound; ten additionally inherit the
existing opaque `core.fmt.Formatter` type. No new axiom or hiding premise.

## Evidence and remaining security proposition

`python3 docs/research/v8-full-view-zk-20260912/tools/check_r100_evidence.py`
checks the parent evidence, source pins, both native runs, negative controls,
trace, instrumented-source generator, all final proof metrics/axioms and the
109-artifact manifest. NUC caps are host/Lean 5/7 GiB, SBF 12/16 GiB, runtime
2/3 GiB and collection 1/2 GiB, always MemorySwapMax=0. All retained process
swap counts are zero. No proof fixtures, ELFs, raw registers or keys are copied
into evidence. The Solana skill's full-source, malformed, stack and runtime
checks remain required selection gates.

The next observer step is **whole source-experiment composition** beyond the
now separately proved circle and selected-query samplers. The first profile
proposition remains universal actual-source C1/H1/G joint affine-image
compatibility for R84, including the channel p0/p2 messages, legal same-public
witness differences, adaptive/degenerate prefixes and justified exception
losses. Finite certificates are not that theorem. Causal posterior simulation,
seed/C2 commitment composition and visible retry/publication remain open.
Soundness separately requires coherent original quotient-pair extraction before
beta and actual shared-oracle/loss accounting. R84 is not security-promoted.
All negative regressions remain; no production-path change, deployment or wallet
operation was performed.
