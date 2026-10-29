# Top-down status (work in progress)

The requested instantiated native theorem is NOT established.
`PV_L2E.trace_simulatable` is a proved forward-simulation schema: each
`PV_L2E_Link_Vxxx` is a standalone Prop about ONE transition and a successor
state relation, never a whole-trace equality. The theorem covers every finite
ordered prefix, including halted and divergent prefixes if the source machine
is instantiated correctly. `PV_L2E_CommonSample.on_existing_join` specializes
the domain to the existing cp.toR/cp.toM and EXACT OffCharged complement.

The schema still has UNDISCHARGED machine, initial-state/canonical-preparation,
and simE/D163 association parameters. In particular, an arbitrary simulator
machine is not evidence about actual simE, and an arbitrary honesty predicate
is not successful canonical preparation. Existing view agreement and equality
in law do not discharge these. This is not counted as satisfying the requested
instantiated top theorem or removing any endpoint premise.

| Link | Status / precise remaining work |
|---|---|
| V353 | OPEN. Bind all expander method calls and their raw seed/rejection words to the same coupled coin history, preserving failures and counters. Reuse L2D source laws, not an independent count marginal. |
| V354 | OPEN in this schema; inherited work has not been instantiated into its machine relation. No new whole-row claim. |
| V355 | OPEN. Uncapped simulator nonzero loop and seed/counter/history association; wrapping/overflow must retain release semantics. L2D helpers retained. |
| V356 | OPEN. New reverse-division, digit and carry trace/value laws; native finite controls. Remaining: byte/array-to-list source binding, all index guards, circle/fallback and canonical decoder paths, transcript call order, and actual raw-block coupling on canonical honest runs. |
| V357 | OPEN in this schema; inherited work has not been instantiated. |
| V358 | OPEN. Need complete eager block/advance sequence and failure-state preservation on the endpoint cp, not accepted query-set equality. |
| V359 | OPEN. Need full producer/source association, global order and same-cp call arguments in addition to inherited zero-tail/Merkle/publication helpers. |
| V360 | OPEN in this schema; inherited work has not been instantiated. |
| V361 | OPEN. TagEch zero skips, pivots, early returns, family/convert dimensions, and ambient transport/hook/worker association. No proof supplied. |
| V362 | OPEN. Challenge-only argument flow is an inspection result, not the complete source and ambient-state invariant. |
| V363 | OPEN. C3 native-kernels/native-workers deployed branch, scheduling, all allocation plans and abort prefixes. |
| V364 | OPEN. Complete checker short-circuit/failure/control sequence under deployed features, including parallel worker ordering. |
| V365 | OPEN. Simulator history/programming/table traversal, retries and ambient state remain to bind; simulator existence does not prove native agreement. |
| V367 | OPEN. Source slot/denominator association, all pole-kernel invocations and retained failures; no additional charged event. |

No checked honest-secret leak has been found. No new T field, old event,
success conditioning, simulator change or observer weakening is used. All
original PV_L2_Premises fields and RustRealRefinement remain unchanged.
Allocator outcomes, after proving request size/alignment/order, retain rdea-1;
source-to-machine-code remains V370. No singleton-input claim is made for
functions that depend on random blocks, transport TLS, hooks, clocks or workers.

Attempt 67900 failed parsing `prefix` as a reserved token. 67901 renames it;
no unchanged failed source was retried. 67904's carry bound proof failed and
67905 replaces it by explicit transitivity. 67908's word reconstruction failed
and 67909 uses the exact scaled identity. 67911's let/if proof failed; 67912
splits the actual carry condition. Failed outputs containing sorryAx are
retained ONLY as failure evidence, never imported as accepted objects.

The new trace models expose their event vocabulary and are partial source
models, not comprehensive native observers. In particular division plans do
not yet insert every Rust indexing/conversion guard. Value comparisons do not
constitute source-step or instruction-trace binding. The finite native harness
uses byte-identical four helper bodies, Rust 1.94.1 -O, no cfg alternatives,
debug assertions and overflow checks off; it is not the full deployed crate or
shipped ELF. Four wrappers expose private helpers; no helper text is rewritten.
