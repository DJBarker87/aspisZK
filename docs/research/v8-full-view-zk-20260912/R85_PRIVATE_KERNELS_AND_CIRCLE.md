# R85: private native kernels and exact observed circle retries

Base: `16c672f16becb0e1cbfeec350c01aa25277b24ba`. Research only.
The user resumed both the under-1M execution target and the full security
proof. Neither target is complete, and R84 remains **unpromoted**.

## Complete unchanged-R84-proof measurements

| Native implementation | World 0 CU | World 1 CU |
|---|---:|---:|
| R84 control | 1,212,653 | 1,210,833 |
| Private quotient kernel | 1,202,355 | 1,200,492 |
| Private ordinary kernel | 1,209,805 | 1,207,999 |
| Composed R85 candidate | **1,199,479** | **1,197,630** |

The composition saves 13,174 / 13,203 CU. Both actual 1,000,000-CU honest
executions still exhaust. The larger complete result is **199,479 CU** over
target. These runs reuse the two exact R84 proofs, not regenerated favorable
fixtures. They are not unchanged-R19/R83 profile measurements.

All three measured variants pass focused source checks, both complete host
verifiers, 3,281 checked malformed-wire rejections plus one acceptance, and
the SBF source-table and stack gates. Heap remains 262,144 bytes. The modified
combined-final controls reject with Custom(6), not resource failure, at both
caps; simulated accounts are unchanged. No deployment or wallet operation.

### Source changes

The retained private canonical `Q` representation now spans complete quotient
and ordinary kernels. Its fields remain private; every public input is
validated at entry. Multiplication uses the retained bounded R69 formula.
Short dots use R59's raw products and four residue accumulators, with at most
four terms and one final canonical reconstruction. No general reducer or
public raw-constructor fallback is removed.

The quotient kernel retains private values through interpolant subtraction,
the four denominator products and the complete normalized fold. It is used
only after the existing decoder, leaf hashing and domain check, and after
successful shared denominator inversion. The old per-record path remains the
fallback. Both commitment roots and paired authentication remain mandatory.

The ordinary kernel retains private values through the two transformed tensor
contractions and four swap-entry evaluations. The original R84 calculation
remains the differential reference and noncanonical-input fallback. The
inactive correction, balancing pivot, chord geometry, sparse G and arbitrary
image/final terms are unchanged.

Focused additional checks cover 8,192 complete arbitrary quotient/fold cases,
4,096 private short dots and 96 malformed array boundary cases. The ordinary
checker compares the private result and all four entries with the retained
kernel on 64 full-field cases, then compares the complete functional with
the independent dense source calculation. Zero/one challenges and arbitrary
final/image values remain included. R83's opening controls remain intact.

The new exact-text trace reproduces the control's 1,212,653 CU and attributes
1,108,295 executed instructions. It records 1,169 general QM31 multiplies,
with 1,061 distinct commutative operand pairs. It is one public execution,
not a universal frequency bound. Function counts are exclusive; inlined work
belongs to callers. Raw register traces stay on the NUC and are not published.

Two early compile failures are retained: a missing test-array type annotation
and a missing M31 import in the ordinary adapter. Neither reached SBF or is
counted as a performance result. The corrected immutable stages are separate.

## Formal result: the circle sampler's complete observed view

Four focused Lean leaves compile, with **12 theorem audits**:

- `SamplerObservedCircleLoop`: the instrumented actual three-attempt outer
  loop equals its bounded form, including arbitrary backend failure/divergence.
- `SamplerObservedCircleBridge`: compose the proved QM31 observer with the
  retained extracted circle map, preserving ordered queries/answers, both
  exhaustion constructors, successful points and advanced state. Erasing
  observations returns the original retained extracted sampler.
- `CachedFiniteSupport`: a finite causal program over arbitrary addresses
  has the exact first-read-only oracle law with an arbitrary existing table.
  Cached and repeated addresses retain their answers. Only potential future
  finite support is randomized, not the infinite byte-address space.
- `SamplerObservedCircleProgram`: the decoded public circle view equals the
  retained memoized program; its ideal-oracle law allows arbitrary prior
  cached answers. The internal backend function pointer is not observable.

These are interpreter/source-correspondence results under the **explicit total
deterministic hash adapter**. They do not prove SHA ideality, independent field
challenges after conditioning on later commitments, or a full source prover
experiment. R79's mechanical instrumentation checker is not a certified
compiler. Backend failure/divergence in `StateT Trace Result` does not return
a separate prefix trace; ordinary sampler exhaustion does retain its history.
The original extracted R72 definitions are unchanged. Refinement of later
optimized arithmetic remains a separate obligation.

| Final exact target (`AspisV8R19/… .lean`) | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| `SamplerObservedCircleLoop` | 0 | 2.97 | 3,711,368 | 0 |
| `SamplerObservedCircleBridge` | 0 | 2.16 | 3,713,268 | 0 |
| `CachedFiniteSupport` | 0 | 1.76 | 3,230,912 | 0 |
| `SamplerObservedCircleProgram` | 0 | 1.89 | 3,715,788 | 0 |

Lean 4.32.0, `lake env lean -j1 -M4500`, 350 reused compiled targets and
358 dependency pins; no dependency rebuild. Four audits use standard Lean
axioms only; eight additionally retain the documented opaque
`core.fmt.Formatter : Type`. No new axiom, admission or final warning.

Failed focused checks are retained. An accidental extra Result lift and a
loop-body rewrite mismatch were corrected. An elaboration timeout was fixed
with explicit generic types. Concrete support elaboration was replaced by a
generic own-support theorem before specialization; no recursion/heartbeat or
memory limit was increased. One final four-leaf replay followed green focused
targets. All heavy work used capped Linux systemd scopes with swap disabled;
simultaneous reservations stayed below 26 GiB.

## Exact open boundary

1. **R84 profile:** universal actual-source C1/H1/G joint affine-image
   compatibility, including p0/p2, legal same-public witness differences,
   adaptive/degenerate prefixes and any explicitly justified exception loss.
   The two passing finite rank/correction audits are not this theorem.
2. **Observer:** source-exact q22 query/rejection history, then composition of
   the whole shared-oracle experiment with seed expansion, both commitments,
   subsequent messages, visible failures, retries and publication.
3. **Privacy:** posterior-preserving causal simulation of that complete view.
   **Soundness:** coherent extraction of the original quotient pair before
   beta, actual challenge law and all extraction/list/bad-event losses.
4. **Execution:** complete under-1M acceptance, followed by the full selected
   source/security release gates. No security parameter or validation check
   may be traded away to meet the budget.

R83 remains the selected unchanged-profile control. R85 is the fastest measured
R84-profile research implementation, not a security promotion. Existing C1,
one-swap H1 and other negative regressions remain unchanged.

Recheck the 159-artifact public evidence bundle without recompiling:

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/check_r85_evidence.py
```

The Solana development skill's source → malformed-input → stack-safe SBF →
complete-runtime sequence was followed. No signing, transaction submission,
deployment, merge or key cleanup occurred.
