# Same-source row-31 list/output bridge

`literal_list_eq_trace_values` combines the literal sampler's `pairsRun = .ok xs` fact with the concrete `scanOut` output for the same eight pair views, proving `out.val.map U32.val = xs`. Its premises retain the pair-list projections to the materialized block/advance lists and the actual `scanOut` result; it does not assert equality with the literal list as an input.

The pair-view premise is a remaining source-witness adapter for the composing caller. The theorem is a small consumer and does not prove that adapter or produce the `scanOut` result. Lean 4.32 focused compile, full profile, resource logs, and axiom audit are retained in `receipt/`. No compiled object is included.
