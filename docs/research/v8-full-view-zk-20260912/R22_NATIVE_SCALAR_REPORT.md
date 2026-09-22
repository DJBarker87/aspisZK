# R22: measured native scalar transpose

## Decision

R21 remains retired. R22 preserves R20's protocol, T163, sparse G, transcript,
image terms and proof format. The candidate is research-only: no production
integration, new proof layer, basis replacement, deployment or wallet operation.

The direct scalar ordinary/image kernel is correct on the executed source tests
and about **2.4% cheaper** in the same SBF executable. This is a small kernel win,
not a solution to the full-verifier budget. The complete R20 endpoint remains
**2,865,333 / 2,866,803 CU**; no new complete-verifier measurement is claimed.

## Pinned comparison

Control revision: `6f00e7f6c893c3a81bc37526e32d563434d303c8` (R20 clean B).
Research parent: `1c14e839c237085c96032e3a9a85ab2ad72f255a` (pushed R21 evidence).
The stager checks all 173 frozen R20 file pins before generating the 179-pin
native comparison. It reuses only R21's public native-input interface, not its
certificate, circuit, helper prover or helper verifier.

Clean comparison ELF SHA256:
`7a4f81f7be0eba715d9867c9a2fc55c37894b8dcbf457c92c65e618ed4e46f9d`.

Both implementations run in this same ELF on identical 400-byte inputs, with
the same 262,144-byte heap. The final 16 bytes are the expected native result,
not an auxiliary certificate.

| Genuine input | Reference ordinary + image | Scalar ordinary + image | Saving |
|---|---:|---:|---:|
| World 0 | 786,908 | 768,140 | 18,768 |
| World 1 | 787,096 | 768,067 | 19,029 |

Both accept at actual 1M and 100M caps. Wrong-output, noncanonical-input and
truncated-input controls reject through checked errors at both caps, in both
implementations and both worlds (24 checked negative executions). These are
isolated kernels, **not complete proof verification under 1M**. The older R21
native interval used a different harness and is not the comparator here.

## Exact computation and correctness boundary

For group `j`, construct `H[j] = high[j & 15] * finals[j >> 4]` and the exact
carry-adjoint `B = xt^T H`. The carry scatter walks the same powers of one-half
as the source, with the source's zero extension at index 64. Contract selected
T163 coordinates into 16 normal and three carry sums, then evaluate their
19-term scalar functional and divide by 256 through eight halvings.

The inactive correction uses the actual transport order and inactive mask.
The original pivot weight and pivot contribution remain. The plain tensor
block is contracted directly with the final four values before returning its
scalar. The image residual calculation is unchanged. Workspace is 531 QM31
values (240 factors, 163 deltas, 128 adjoint factors), not a transposed dense
1024-vector. Ordinary/G geometry sharing is **not** integrated or benchmarked.

Executed checks:

- 256 arbitrary full-QM31 source comparisons, including zero, one, maximal
  canonical limbs and arbitrary final/image values.
- 4,096 coordinate-basis comparisons against the actual source kernel.
- Both genuine captured public-input sets; output bytes also match the earlier
  source-captured native results.
- All 4,096 entries of the carry transpose checked exactly over integers after
  multiplying by 64, including the longest six-half chain and index-64 boundary.
- Host and clean/profile SBF release compilation succeeded, without a stack
  frame overflow diagnostic.

The matrix calculation is an exact finite algebra check. It is **not** a Lean
proof of all Rust semantics. No Lean targets changed or compiled; no new
privacy, soundness, Fiat–Shamir or source-refinement theorem is claimed.

## Executed instruction evidence

World-0 register traces reproduce the non-traced clean CU exactly. The deployed
ELF is SBPF v0. Categories below count executed instructions, not source-level
field operations or guessed CU charges.

| Category | Reference | Scalar | Reference minus scalar |
|---|---:|---:|---:|
| All instructions | 785,332 | 767,254 | 18,078 |
| Shifts | 216,429 | 206,060 | 10,369 |
| Branches | 129,052 | 125,071 | 3,981 |
| Bitwise | 27,543 | 23,579 | 3,964 |
| Integer multiplies | 25,190 | 25,852 | -662 |
| Loads | 65,102 | 64,442 | 660 |
| Stores | 37,577 | 38,054 | -477 |

The scalar improvement is not explained by fewer executed multiplies. It has
more. Do not label every shift a field reduction or every branch a bounds check.

The stripped clean ELF lacks function symbols. One hot function was positively
identified through a **unique exact 344-byte match** to the named `__multi3`
compiler builtin in the unstripped profile ELF. The function has no relocated
call instruction. Its clean PC starts at 95186 and spans 43 instructions:

- Reference: 2,887 entries, 124,141 executed instructions.
- Scalar: 3,088 entries, 132,784 executed instructions.

This identifies wide-integer multiplication as a concrete executed cost, not
its source callers or a safe replacement. Establishing those callers and their
integer bounds is the next attribution obligation. Do not disable overflow
checks or replace general reducers based on these counts.

## Instrumented phase evidence (world 0)

These are marker-to-marker differences in a **different instrumented build**;
they include marker overhead and changed compiler layout. Clean totals above
remain the acceptance evidence.

| Region | Reference | Scalar |
|---|---:|---:|
| Chord geometry | 38,873 | 38,873 |
| Setup / point factors | 28,684 | 25,766 |
| Tensor factors | 135,468 | 135,468 |
| Plain contraction | 102,787 | 100,042 |
| Scalar adjoint geometry | — | 48,300 |
| Permutation value + contraction intervals | 376,440 | 349,637 |
| Inactive interval / scalar inactive-pivot-final interval | 90,603 | 61,617 |
| Image and final dot interval | 13,845 | 8,237 |

The inactive rows are not identically bounded phases: the reference pivot work
falls into its following interval. Likewise, the reference permutation-values
marker precedes `cycle`, while the scalar marker follows it. Therefore compare
the combined permutation intervals, not those two subintervals independently.
The scalar has another 247-CU marker boundary after the plain contraction.
Instrumented total: 788,769 / 770,261 (reference / scalar) for world 0;
788,957 / 770,186 for world 1.

## Reproduction and evidence

Tools: `stage_r22_native.py`, `run_r22_native.py`, `run_r22_svm.py`,
`analyze_r22_trace.py`, `collect_r22_native.py`, `check_r22_adjoint.py` and the
four `r22_*.rs` files. Staging requires the pinned assembled R20 clean workspace,
not merely an arbitrary checkout at the R20 revision. Run builds with the
repository's bounded Linux-host scopes and cached dependencies.

Compact receipts, manifest hashes, compile logs, `/usr/bin/time -v` resource
reports, negative results, trace summaries and driver lockfile are retained in
`evidence/r22-native/`. Large raw register/instruction traces and executables
remain on the NUC at the receipt's exact stage paths; their hashes are retained.
Keys were not copied or removed.

Tracing required enabling LiteSVM's diagnostic `register-tracing` feature.
The preflight lock/cache failures are retained. Only optional `hex 0.4.3` and
`nom 8.0.0` packages were added; all original locked package versions/checksums
were checked unchanged. The missing `nom` was fetched before the successful
offline locked release build. Program dependencies were not changed.

The Solana testing workflow guided source checks followed by capped LiteSVM
execution and register traces. No validator deployment or live transaction ran.

## Remaining boundary

This completes the requested **native comparison**, not the overall CU target.
Before installing the small winner, the complete verifier must pass unchanged
proofs and adversarial tests and demonstrate its actual whole-execution saving.
Before claiming a larger win, attribute the wide-multiply call sites, prove any
narrower integer bounds, and measure the replacement. Semantic, opening and
other native costs remain. The short-cycle basis and resumable verification
were not installed. Existing privacy and soundness obligations remain open.
