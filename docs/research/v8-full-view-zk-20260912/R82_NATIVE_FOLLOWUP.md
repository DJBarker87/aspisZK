# R82: compose native arithmetic wins; retain measured regressions

2026-09-29. Follows pushed R81 `9e0f3964610e74284510d81066971b339c124bdd`.
Same repaired protocol, two frozen proofs, driver, heap and acceptance checks.

| Experiment | World 0 CU | World 1 CU | Decision |
|---|---:|---:|---|
| R81 control | 1,356,211 | 1,357,487 | Reference |
| Ordinary two-product entries | 1,346,806 | 1,348,070 | Compose |
| Inline generic multiplication | 1,356,726 | 1,358,040 | Reject regression |
| Packed opening affine sum | 1,354,455 | 1,355,729 | Compose |
| Entries + affine + checked low contraction | 1,336,800 | 1,337,989 | Compose |
| Also unroll basis powers | 1,350,300 | 1,351,489 | Reject regression |
| **Also inline checked dot** | **1,333,812** | **1,335,001** | **Selected** |
| Cached multiplier matrix, without dot inlining | 1,335,293 | 1,336,491 | Tested, not selected |

The selected endpoint saves **22,399 / 22,486 CU** against R81, and about
162k against R69. **Both honest proofs still exhaust at the actual 1M cap.**
The larger fixture remains 335,001 CU above target. No sub-1M, universal
resource bound, settlement execution or completed security proof is claimed.

## What changed

R62's two-product entry organization was previously slower. R81 replaced its
underlying short-dot implementation, making a new measurement justified:
the same two tensor entries now share final canonical reductions. The old
entry stays as the differential oracle; 262,144 coordinates are compared.

The packed opening's `value + dot3(helpers)` uses the affine short dot, which
includes the canonical constant before its final reduction. Decoding and
error order are unchanged, including all limbs at beta zero/one. The final
16-term low contraction uses the retained checked dot with its original
fallback. Inlining that checked dot saves a further 2,988 CU on each fixture.
It does not remove the length, term-count or limb guards.

Inlining generic multiplication and unrolling the power schedule are both
source-correct, stack-safe, but slower in complete execution. They remain
recorded and are not installed. The cached-matrix experiment precomputes the
canonical linear multiplication matrix in a private constructor, using the
existing four-product u64 bound and retaining the raw-input fallback. It
passes but does not beat the selected endpoint; it is not silently composed.

All seven candidates pass the retained square/product/prepared/short-dot,
semantic-basis/private-kernel, ordinary/gather/tensor/sparse-G tests and all
3,281 wire controls. Both honest diagnostic executions accept; malformed
finals produce a checked rejection. Actual 1M exhaustion is not called a
security rejection. Overflow checks remain enabled and no SBF frame
overflow diagnostic is accepted.

## Evidence and boundary

`tools/check_r82_evidence.py` audits 202 artifacts, 210 exact source pins per
candidate, unchanged proof and driver hashes, allowed source deltas, build
and execution logs, time/RSS/swap and actual cgroup limits. It also checks the
parent R81 evidence. Heavy jobs use the cached Tailscale NUC with swap disabled
and host 5/7 GiB, SBF 12/16 GiB, runtime 2/3 GiB high/max limits.

The composed pre-inlining trace exactly matches its clean 1,336,800 CU.
Generic multiplication accounts for 193,292 exclusive instructions; checked
dots 116,149; the opening caller 110,106; packed combination 103,642; ordinary
caller 82,926. Inlined work remains charged to its caller. These counts are
not separate inclusive CU budgets or a claim that any whole interval vanishes.

No new Lean work, masking change, T163 change, transcript change, new hiding
assumption, validation removal, deployment or wallet operation. The Solana
skill's actual-source → stack-safe SBF → complete runtime gate remains in use.
Existing full privacy/soundness obligations are still open. Next work remains
native execution, particularly reducing ordinary tensor/contraction work;
the under-1M target has not been achieved.
