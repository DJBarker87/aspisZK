# Callback mid-row work

Candidate base: 237e13556180d2ce0320a2760f89b35b5f4f02bb (unmerged).
Target not yet established. Rows discharged: 0 → 0.

| op | row | status | theorem | receipt |
|---|---|---|---|---|
|132|V228|P6 required: built MIR extracted; pinned Aeneas rejects escaping references/structured Drop|none|charon-op132-002/receipt.json; aeneas-op132-001/receipt.json|
|133|V229|P6 required: built MIR extracted; same explicit backend rejection|none|charon-op133-001/receipt.json; aeneas-op133-001/receipt.json|
|134|V230|pending; shares schedule/iterator graph with op133|none|pending|
|79|V201|pending|none|pending|
|222|V239|pending sibling ownership recheck|none|pending|
|224|V241|pending sibling ownership recheck|none|pending|

All six source-law searches returned no matches on codex/pv-cb-20261026,
codex/pv-cb3-20261026, and codex/pv-cblib-20261027 before work began.
Frozen shipped code unchanged. No premise removed, added, or weakened.
No source counterexample has been observed. Extraction failures are not counterexamples.
The owned references require independent complete shipped/reference Kani checks
before any row can be credited.

Host cache: cb3/lean-objects absent. PROVENANCE.json records exact matches for
all inspected source/manifests in the three reused crates. No sibling directory
is edited. The own wrapper is cfg(kani); it imports hash-checked source read-only.

Next: independent P6 inventory references and exact equality harnesses; focused
op79 extraction with a narrower dependency graph. Lean budget 1/100, Kani 1/10.

40600 compiled InventoryShape: three prerequisite classification theorems,
all axioms [propext]. This is a model prerequisite, not a callback/source law.
The complete mask native gate timed out at 180s, exit124; no verdict or
counterexample. No unchanged retry or raised cap is authorized.
Op79 built MIR also extracted but Aeneas rejected the same explicit graph
features (aeneas-op79-001).

The owned mask reference extraction succeeded (aeneas-op134ref-001), including
the concrete error carrier and all 64 values. Its selected-reference theorem
is explicitly named `op134_reference`; it is not `op134_source`, and is not
credited as V230 closure. Bundle stable name: PV_CBM_CallbackBundle.

Admission ID40601 refused (projected 60,532,195,328 bytes > 55 GiB limit);
zero compiler charge. Wait 180 seconds, then use the next unused ID. Earlier
op79 upload admission hit a vanished unrelated session cgroup, retained in
admission-state.json; special transient wait was 30 seconds and retry succeeded.

## Checked prerequisite stage

InventoryCardinality.cardinal proves the mathematical classification has exactly 3803 cells (40624). Padding/path/value bijections passed at 40618/40621/40623, with standard axioms, swap0. This is a model/count prerequisite, not the shipped callback law.

Native classifier: kani-classifier-001 passed (0/61 failed), exact frozen source-prefix child harness vs owned classifier, all 1024×16 valid inputs, unwind25, no stubs. Full masks gate180 timed out; ruling(i) now permits one 900-second retry with identical bounds/caps.

Current tally: Lean 20/100, Kani 2/10; next Env-J ID 40627. Last three charged Lean attempts remain reserved. No ROW counterexample. Rows0→0 and endpoint premises unchanged.

## Mutable-output reference extraction

Owned-by-value Vec functions were refused:61 declarations contain structured Drop (CELL-DROP-INSPECTION.json). No Drop was removed. The reference now uses unique mutable output parameters; the native wrapper retains vector ownership and destructors. Charon and Aeneas accepted fill_cells (charon-op132fill-001, aeneas-op132fill-001). Aeneas emitted owned Vec states and a complete Rust-result/state pair.

prepare_cells.py --check passes. Generic PushList and Result right-identity lemmas compiled; first chunk fixed by equation rewriting and the named complete-Result right-identity theorem (no limits raised). Remaining chunks are independent, serial, first-time compiles; all staged pending modules are explicitly uncredited until their receipts pass.

Checkpoint tally: Lean38/100, Kani3/10; nextID40652. Last3charged slots and IDs40897-40899 reserved for audit. Rows0→0.
