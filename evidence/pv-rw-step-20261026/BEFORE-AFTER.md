# Before/after and retained obligations

Branch `codex/cx-prover-rw-20261023`; base `5d97a425c5`.
This is the unmerged prover candidate. The privacy target is not established.

| Obligation | Before this allocation | Checked after the focused pieces | Removed row? |
| --- | --- | --- | --- |
| V164 / op223 V240 | Owned/list reference equality available; shipped compression correspondence absent; previous unchanged whole-loop Kani attempts unusable. | Literal emitted arithmetic step, actual Std iterator/initializer, and combined iterator/arithmetic transition are connected to an actual Aeneas loop. That composed loop equals a closed owned reference for arbitrary slices and typed arity16, with full `(out,power)` state, full Result, sufficient17 control bound, totality, and final power projection. | No. Association of the original whole Rust helper to this composition remains open. The whole-helper Aeneas probe failed. The native state/coordinate Kani gates timed out. |
| V163 | `data (execute …)=model` is supplied to `BodyData.refinement_of_data`; model arbitrary. | The composed compression equality is consumed by auxiliary dictionary equality, the complete proof/audit caller, and `CombinedBodyData.refinement_of_data`. The missing whole-data equality is equivalently split into exact proof-byte and audit observations, preserving both error layers and divergence. | No. Neither component comparison to a concrete security-model term was established. No model was defined to equal source output. |
| V257 / op250 | Source-policy sampler equality retained; native traversal association open. | Passed native limb/array-state/iterator/parser/decoder pieces; emitted limb and array step, reverse pass, index/remainder invariants, totality and finite bound linked to retained references. | No. Complete ordinary sampler assembly/effect/source association and live callback join are retained. |
| Other callback rows |31 inherited callbacks open (V262/op255 and V255/op247 already supplied in rw16). | Read-only sibling checks, latest pv-cb head recorded; no live callback installation here. | None. Assigned/supplied sibling work skipped. |
| Endpoint and deployment conditions | Supplied prover/model correspondence, E1/E2, RunJoin, L1/L2/L3, proof-account client route, native representation/effect and coherent release replay conditions remain. | No endpoint, simulator, observer, release pin or production source changed. Cached focused audits do not establish a frozen source/release replay. | None. |

No endpoint premise was added, renamed, weakened or removed. Auxiliary transport
changes a dictionary in a still-explicit data comparison to a proved equal
closed owned dictionary. It does not assert that dictionary is the live native
one. Source/ABI/features/effects and release obligations remain visible.

The next deliverable is a checked association of the original helper's for-loop
context to the emitted combined-transition loop (initializer, iterator state,
all arithmetic updates and final power update included), then a live op223 join.
V163 then needs the concrete model term and proofs of both byte/audit comparisons.
The unanswered model clarification is not inferred from elapsed time.
