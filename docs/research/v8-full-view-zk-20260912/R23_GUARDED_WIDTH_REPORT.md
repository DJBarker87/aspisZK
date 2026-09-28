# R23: guarded integer width — complete-verifier saving

2026-09-28. R21 stays retired. No new proof system or privacy-profile change.

## Measured outcome

The complete R20 verifier with **two guarded multiplication sites changed**
accepts the same two frozen proofs at **2,529,453 / 2,530,968 CU**. This saves
335,880 / 335,835 CU (approximately 11.7%) against clean R20. Both actual 1M-cap
runs still exhaust: the budget target remains **OPEN**.

| Same public fixture | R20 clean B | Guarded width only | Saved CU |
|---|---:|---:|---:|
| World 0 | 2,865,333 | 2,529,453 | 335,880 |
| World 1 | 2,866,803 | 2,530,968 | 335,835 |

The 256 KiB heap, driver, fixtures, transcript, proof format, sparse G, T163,
image constraints and verifier acceptance checks are unchanged. **R22's scalar
transpose is not included in these complete-verifier totals.** No reference
removal, whole-dot or earlier R20 saving is counted again.

Control: `6f00e7f6c893c3a81bc37526e32d563434d303c8` plus its frozen 173-file
assembled-source manifest. Research parent: `fbd5e9ac362b16713f828c1a1508af497d5d9e6d`.
The complete candidate has 174 source pins: one modified field source and one
new helper; all other control files remain byte-identical. Native comparison
has 182 pins including its test/reference sources.

## What caused the cost, and what changed

The source CM31 multiplication and squaring kernels multiply unreduced sums
as `u64` operands. With overflow checking, the observed SBF compilation calls
the wide-integer multiply builtin `__multi3` thousands of times. The rewrite
guards the operand widths:

```rust
if left <= u64::from(u32::MAX) && right <= u64::from(u32::MAX) {
    u64::from(left as u32) * u64::from(right as u32)
} else {
    left * right
}
```

For the fast branch, both casts are exact and
`left * right <= (2^32 - 1)^2 = 2^64 - 2^33 + 1 < 2^64`.
Thus its product equals the original mathematical product without overflow.
The other branch executes the original multiplication, including overflow
panics when checks are enabled. This guard is valid for **all u64 operands**;
it does not depend on silently treating arbitrary constructors as canonical.

Canonical CM31 inputs hit the fast branch: addition factors are at most
`2P-2`, and the square's `a+P-b` factor lies between 1 and `2P-1`, both below
`2^32`. Surrounding sums, subtraction, reductions and validation are untouched.
No global overflow checks or general full-width reducer were disabled.

This is an elementary bound and source rewrite argument, plus executed checks,
not a new Lean theorem or a universal Rust-to-machine-code refinement proof.

## Actual instruction attribution

R22's identified builtin has 43 instructions. A unique exact-byte match locates
that same builtin in the candidate ELF; the existing raw traces and new traces
give:

| Native path, world 0 | Helper calls before | After | Kernel CU before | After |
|---|---:|---:|---:|---:|
| Existing four-output contraction | 2,887 | 4 | 786,908 | 654,299 |
| R22 direct scalar contraction | 3,088 | 4 | 768,140 | 624,225 |

World-1 after values: 654,494 / 624,162 CU respectively. All native negative
controls still reject correctly. Traced CU exactly matches non-traced CU.

For the existing kernel, the rewrite removes 132,609 executed instructions:
48,388 moves, 25,927 shifts, 17,288 add/sub instructions, 14,412 integer
multiplies, 8,315 loads, 6,436 stores, 6,011 branches, 2,940 bitwise instructions,
and 2,883 calls plus 2,883 exits; immediate loads increase by 2,874.

Attribution is a controlled two-site source perturbation, exact builtin-byte
identification and executed trace comparison. Original predecessor-PC counts
are retained. This is not a guessed mapping of all machine instructions to
source lines. Four residual helper calls remain unassigned; no elimination of
all wide arithmetic is claimed. Neither the original two-profile R22 ELF nor
these isolated kernels are treated as full-verifier measurements.

## Checks executed

- Host and SBF release compilation succeeded; SBF overflow checks remain on.
  Focused host tests explicitly enable them as well.
- 200,000 arbitrary canonical QM31 pairs and 1,296 boundary pairs compared
  multiplication and square against the untouched R20 field source: 402,592
  field-result comparisons.
- 64 raw u64 product cases: exact results or the expected checked overflow,
  including 15 caught overflow panics.
- Native kernel: 256 arbitrary source comparisons, 4,096 coordinate-basis
  checks, both genuine public inputs, and unchanged captured result bytes.
- Complete host verifier: both genuine proofs pass; independent host reference
  is retained. All 3,281 wire controls pass, including 2,796 noncanonical limbs.
  No old-profile fixtures were supplied to this run.
- Complete SBF: both honest proofs accept at the diagnostic cap; both corrupted
  final-message controls give checked custom rejection at that cap. At the
  actual 1M cap, both honest and corrupted proofs exhaust. Exhaustion is **not**
  counted as checked rejection. Simulated accounts remain unchanged.
- Every source pin is checked before execution. No unchanged large formal
  regression, Lean build, deployment, live transaction or wallet operation ran.

The Solana testing skill determined the source-gate → capped LiteSVM → trace
workflow. All heavy work ran on the NUC via Tailscale in swap-disabled scopes:
5G high / 7G max for builds, 2G / 3G for runtime, 1G / 2G for analysis. Logs
retain commands, exit status, wall time, peak RSS and process swap counts.
Unrelated host work and existing keys were not modified.

One host launch initially used `r19-host` (the retained executable's name)
instead of Cargo's `aspis-v8-performance-host` target. It failed before
compilation; the corrected launch and failure log are both retained.

## Reproduce / inspect

`tools/stage_r23_width.py` stages the focused comparison from the frozen R20
workspace. `tools/stage_r23_full.py` stages the full verifier using the exact
tested helper and field source. It does not copy the scalar transpose into the
full verifier. `tools/run_r23_full.py` runs the host, SBF and SVM gates; invoke
each inside the repository-prescribed capped scope. Existing R22 native
runners and R20 build/driver caches are reused, not independently reimplemented.

`tools/check_r23_evidence.py` checks the retained compact artifact manifest and
can compare every candidate source pin against a local staged reconstruction.
`evidence/r23-width/` contains the exact field diff, helper, source manifests,
compile/runtime logs, public fixture hashes, raw-trace hashes, instruction
analysis, full results and failed preflight. Large raw traces and executables
remain at the exact build-host paths in its receipt; no key material is copied.

## Remaining boundary

This is a reproducible **complete-verifier arithmetic improvement**, not a
production deployment or a privacy/soundness completion. The existing security
obligations remain open. Under 1M still requires about 60.5% less execution.

The next bounded optimization is to compose R22's scalar contraction with the
guarded-width full verifier and measure the whole result; its isolated saving
cannot simply be subtracted from this total. Further width/invariant work
must preserve invalid-input and overflow behavior, prove local integer bounds,
and beat this new complete-execution baseline. Do not restart auxiliary proofs
or install a different basis to claim a CU improvement.
