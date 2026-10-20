# Q::raw source and checked map bridge (V5/V6)

This packet preserves the focused source/extraction and Lean evidence for `canonical::Q::raw`, plus the first actual U64 partial-fold-to-Nat bridge. It is a source-only packet: compiled `.olean` files are deliberately excluded.

## Proven results

- Charon and Aeneas successfully processed the focused source cut at V5 with the original local partial-closure body intact and only the function-item callback `.map(u64::from)` expressed as an equivalent capture-free closure. Both capped stages exit 0. This demonstrates that the earlier hoist was not needed for extraction. Original Rust callback/function-item source identity remains a separate boundary.
- The cleaned generated owner uses the selected checked `Array.map` model; it does not import the generated external template. The model consumer compiles and its `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. A separate Lean theorem proves callback-model equivalence between the original function-item model and extracted capture-free closure model. This is model-level operational equivalence, not full Rust std source refinement.
- `qRawPartial_success` proves the actual extracted `closure_2` partial-fold call returns a U64 whose value is `RawReducer.foldBits x.val` for every U64 input. Its audit is standard-only. This closes the exact mask/shift/wrapping-add closure but does not yet link the entire `Q::raw` body to V15’s four Nat coefficient formulas.

## Evidence

The V5 Charon/Aeneas receipts, commands, environments, logs, and exact input/source pins are under `extraction-v5/runs`. The V6 map-model source/config and per-stage preflight/receipt/log are under `lean-map-model-v1`. Callback equivalence is under `lean-map-callback-v6`. The V7 partial fold proof source and receipt/preflight are under `lean-partial-fold-v7`. Exact retained `Array.map` model and `RawReducerNat` sources are in `dependencies`.

All later failed V1-V8 proof attempts are retained in their original unique `/tmp/root-canonical-qraw-partial-fold-v*` directories and were not overwritten; the accepted bridge is V7.
