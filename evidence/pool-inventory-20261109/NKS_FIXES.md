# Inventory script repairs and limits

No compiler, prover or host scope failed or was launched.

- Initial git add was refused by sparse checkout; added only the assigned evidence directory with git sparse-checkout add, then committed.
- Exploratory AST/MIR parser rejected build.rs at module-path splitting (IndexError: list index out of range). Own code now accepts files outside /src/; no shared tooling changed.
- Removed mistaken function-item candidates from bound local variables; direct function arguments and monomorphized function items are retained instead.
- Added optimized-MIR inlined scopes after the source/compiled guard audit showed the stack-height helper was inlined. Restricted entry dispatch edges to actual direct source callees so OFF initialization descendants are not introduced by entry inlining. Every conservative trait/name alternative stays visible.
- Matched trait default bodies and ambiguous source headers conservatively; never guess a unique owner. Generated constructors/derives and SDK/std remain separate boundary records. No custom opaque body is labelled proved.
- Finalized reports use613/119/494, superseding exploratory counts. Earlier parser runs were unscoped exploration, not formal receipts; their resource metrics/source snapshots were not captured and no proof credit relies on them. Six wrapped Python runs retain full receipts. Current and prior report/runner inputs are committed.
- D diagnostics now quote the actual predecessor logs. Family failures are not attributed as a prover run on every D row. No timed-out shape was replayed, timeout increased or memory cap raised.
- The estimate uses1–2 helper rows per successful predecessor job only as a conditional sensitivity range. Zero whole-Pool throughput supplies no empirical finite upper bound; D remains unbounded.
