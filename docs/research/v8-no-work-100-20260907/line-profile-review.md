# Current selected-build profile

2026-09-09, quiet source checkpoint
`074daa2fd0636a577f87bb84075e9ad6fd4f5662`. The four deterministic seed1
maximum-body proofs use the same pinned Pool/Registry/Token/driver and the
actual1.2M limit. Only logging flags change. The quiet ELF is not overwritten.
See [exact intervals and artifact identities](line-profile-results.json).

The profiling ELF is1,012,792 bytes, SHA256
`f8722d05a640cc55128be2ac7bbcccd5ea323a557b61c860cf682fd1ab87d517`.
It costs **24,019–24,100 CU more** than the same quiet executions. Its115
checkpoint pairs and compiler/layout effects make these diagnostic counts,
not selectable complete-CU results. No subtraction of a presumed fixed log
cost is presented as a measured quiet component.

Representative maximum withdrawal-rollover seed1 intervals:

| Interval or explicitly grouped intervals | Instrumented CU |
|---|---:|
| Canonical fixed parsing | 34,555 |
| Semantic rounds | 84,636 |
| Semantic terminal, including selectors/copy/blend/return | 210,386 |
| OOD/gamma and ordinary/image preparation | 75,460 |
| Query schedule and point generation | 18,890 |
| Packed C1/C2 decode, gamma dots and intervening logs | 163,010 |
| Leaf hashing/order | 15,817 |
| Internal authentication | 129,074 |
| Denominator/numerator construction | 23,901 |
| Joined inverses and returned base slice | 32,256 |
| Quotient products and four-slot folds | 37,619 |
| Query injection and subsequent relation responses | 15,369 |
| Query weight and final coefficient folds | 62,052 |
| Grouped and structured terminal, final equality/return | 95,790 |

The listed intervals sum to998,815. The remaining117,305 of this
1,116,120-CU **instrumented** transaction is outside the start-to-terminal
interval, including account/caller handling, CPI boundaries and settlement.
The quiet same proof is1,092,063 CU. The maximum across quiet seed1–3 is
1,092,232, unchanged by this diagnostic.

This confirms that inversion-only tuning now addresses a relatively small
fraction. Authentication and gamma remain substantial, and there are still
measurable final coefficient/weight calculations. The next bounded arithmetic
control expands the existing quotient butterfly into the already supported
three-product sum, aiming to share reductions. It is a new downstream fold
layout, not a retry of the rejected four-channel gamma fusion.

The profile build passed: exit0,34.15s,592,784KiB peak RSS,zero swaps under
High5/Max7GiB/jobs2/SwapMax0. Four SVM scopes used High3/Max4GiB/SwapMax0.
No changed Lean dependency or new crypto claim required a proof replay.

Reproduce on the pinned task COPY with exact074daa2f source/overlays:
`ASPIS_LINE_PROFILE=1 run_complete_build_nuc.sh line-norm NEW_LOG`, then
`run_current_profile_nuc.sh NEW_OUTPUT` with the pinned successful Token3.5
environment. `audit_line_profile.py` reconstructs all interval sums and checks
same proof, programs and cap. Profiling a changed source requires a new named
control; the exact line-source guard refuses silently changed code.
