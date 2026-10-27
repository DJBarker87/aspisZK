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
op79 extraction with a narrower dependency graph. Lean budget 0/100, Kani 0/10.
