# Nested-circle 48-block termination

`experiments/NestedCircleTermination.lean` is checked, NUC v2, exit 0,
with nine standard-only axiom audits. It imports only the frozen
`NestedCircleRunRefinement`; no imported artifact or cache boundary changed.

The budget is literal controller-state arithmetic:

| State | Remaining read budget |
| --- | --- |
| first phase | `4*(3-inner) + 36 - pending.length` |
| second phase | `4*(3-inner) + 12*(2-outer) - pending.length` |
| accepted or aborted | `0` |

The checked Ready invariant gives `pending.length<4` in a live state.
The leaf proves budget positivity and strict decrease on every live
`afterAnswer` step. Waiting consumes one pending-block position. Successful
ordinary calls advance the exact inner/outer controller branch; early
acceptance skips unused retry slots. Hard failures halt immediately.
No padded unread block is counted as a source read simply because the
budget bounds the remaining work.

The initial budget is exactly 48. List induction proves
`Halted (run circleMap initial tape)` whenever `48≤tape.length`. The final
corollary combines this with the checked exact source-result refinement:

```text
sourcePair circleMap tape = none
  iff ∃ reason, run circleMap initial tape = aborted reason
```

The adequate-tape guard is essential. Short-input waiting is not identified
with hard failure. The theorem leaves the concrete abort reason unchanged,
and does not assert that the two model-only impossible branches occur.

These are 48 squeeze-output blocks. The paired duplex-advance coordinates
are distinct oracle calls, not included in that count. Post-halt fold
updates are state-preserving ghost padding. No finite measure, named-slot
coupling, fresh-oracle law, or Fiat–Shamir statement is claimed.

Working parent: `e969d9fa5378dd1e548c8b64b79a9e76a2270d66`.
Borrowed V7 pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
Direct imported source SHA:
`eb96292716d7113f21a8ccaa22f1605f12a9d4a8595670a5db963d52ab8348bd`;
green olean SHA:
`6207695054996c0d73f35873fc4453d68eba082ef7bce7e332dbb1175ea4e170`.
Its whole import closure was already pinned in the inherited NUC overlay.
No import staging or cold dependency replay was needed.

## Focused build evidence

Both attempts ran under explicit serial root grants, through Tailscale
numeric IP `100.108.41.90`, using the inherited `run_higher_y_nuc.sh`.
Preflight reported only `init.scope` and 43 GiB available. The exact Lean
4.32.0 command (`-j1 -M9500`, target `NestedCircleTermination`) and cgroup
settings are retained in each log: MemoryHigh 8 GiB, MemoryMax 10 GiB,
MemorySwapMax 0, CPU quota 200%.

| Attempt | Exit | Wall seconds | Peak RSS KiB | Swaps | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| v1 | 1 | 3.57 | 6655872 | 0 | Symbolic live-budget arithmetic checked; halted-budget branches needed explicit definition reduction, and three `run` unfoldings needed namespace qualification. |
| v2 | 0 | 4.40 | 6687196 | 0 | Only those local reductions/qualifications changed; all nine audits standard-only. |

Every `.log`, `-source.txt`, and `-manifest.json` is retained under
`experiments/nested-circle-termination-nuc-vN`. Failed v1 temporary
`sorryAx` entries are diagnostic only; none occur in v2. The successful
source is byte-equal to its exact snapshot. Final postflight verifies
885 entries and records unchanged provenance. The compiler slot was
released after the terminal postflight, before artifact copying and report
finalization; no other target was run.

The inherited runner scope parent is
`289d7356c78a4cd493fe61a54f9548f2a0c11298`, distinct from the working source
parent above. Native package artifacts remain a pinned-revision cache
boundary, not a package compilation replay.

Final SHA-256:

- Source/snapshot: `21f1c5cdd66868e6c86deda0a5b01c34b303cd08240dec9b1c04defac81860a2`.
- Olean: `7cc55284aa2ace49a734363c24566807731f6b4ceee19cc822497630534663c9`.
- Log: `9f00dd70d296cc4231063e47e1a5f7101319d2ead3672b3e2dd0e04d4438890e`.
- Manifest: `0d2a686a1a201d4f0ec38bedff3c33182ba3524ff8505b7ae0e11ae0902a4e6e`.
- Runner: `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.
