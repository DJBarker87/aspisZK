# D545 / D549 K-3 audit artifacts

Start with K3-ROWS.md (all 34 current row scopes), K3-CREDITS.md (all 305 observations), REPORT-D549.md and D549-RESULTS.json. ROW-COVERAGE.md retains the complete original 407-row review. The ledger is unchanged.

PINS.json freezes entry branches. All other Git source/receipt reads use git show; SOURCE_INDEX.json records byte-hash provenance. RECOVERED.json is the unfiltered early receipt inventory, including failures and codegen-only jobs. Current source resolution is CREDITS.raw.json.xz plus SOURCE_INDEX.json; CREDITS.json.xz carries selected-harness inventory and recommendations. The original complete264-observation K-1 census and source associations are retained in inputs/.

Classifier source and the four requested inputs are pinned to ab9c588335. NEH_check.py ran once before application and passed29 diagnostics plus its boundary checks. Six selected standalone Cargo/module closures are documented separately in SELECTED-STANDALONE-SCOPES.json. No unknown macro or stub is cleared by a source name alone.

Read-only recovery additionally checked retained original-origin paths and immutable per-run updates.json files. These recovered three and seventeen further exact Rust hashes after the shared K-1 scratch workspace had been overwritten. Every byte is SHA checked; a same-name current file never replaces a missing original. Recovery payloads and mismatches are retained compressed.

CONTROLLED-PAIR.json and host/K79200,K79201 retain the single new positive/control pair, all admissions, profile/features, source hashes, limits, logs and resource measurements. STD-PARITY.json and its source captures explain why deployed transfer remains withheld. CACHE-CLEANUP.json records removal of only owned rebuildable cache; sources/receipts/symbol JSON remain. No task keys were generated or removed.

The initial two-run report used report.py followed by finalize.py. These old scripts must not overwrite D549 dispositions. Current reports use d549_report.py followed by d549_rows.py. classify.py only applies the unchanged source classifier; it invokes no compiler or solver. scope_standalones.py and scope_pathbuf.py check package scoping. std_parity.py is source-only parsing and uses the recorded existing tree-sitter packages. validate.py checks hashes, coverage, policy fields and controlled results, without compiling. The committed VALIDATION.json is its result.

D549 continuation receipts are authoritative after the initial pair. D549-RUN-PLAN.json and D549-REFUSALS.json distinguish logical configs, consumed IDs, charged compiler attempts and uncharged admission refusals. D549-VALIDATION.json is the final artifact audit; VALIDATION.json remains the historical initial-checkpoint validation. Source payloads (.json.xz plus uncompressed hashes) retain every input needed to reconstruct the decoded snapshots; v185-source/ is only a redundant decoded mirror of the committed payload.
