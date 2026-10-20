# Terminal `from_fn` source adaptation candidate v2

Status: source-only and uncompiled. The base revision and exact source hashes are recorded in `manifest.json`. This candidate adds `array_from_fn_copy` to an isolated copy of `aspis-core` and updates five source calls in the current terminal path: the 84-element claims selector and four selected-claim gathers in `composition_parts` (three arrays of length 16 and one of length 10). Each callback body and increasing index order is preserved; the helper starts with `QM31::ZERO` and writes every element before returning.

Existing green Lean support covers the copied helper semantics: the claims callback source slice is stable for all 84 indices and its output matches the extracted copy helper; `CompositionPartsGatherStable` proves the four composition gathers with their exact generated callbacks, subject to its explicit canonical-QM premise. Receipts and source/object pins are listed in the manifest.

This candidate has not been built or re-extracted. It only removes five direct source calls. Nested `state_only_poseidon` callees still contain `core::array::from_fn`, so the external-template axiom remains reachable in the whole terminal path. Rust standard-library `from_fn` remains unverified; the source candidate avoids it at these call sites rather than claiming a theorem about its body.

## Remaining call-site inventory

In the v10 generated Funs file, other direct `core.array.from_fn` calls remain inside nested source functions, including `composition_parts` (these four are the additional sites changed in this v2 candidate), `state_only_poseidon.evaluate_state_only_poseidon_oracle_projected`, `external_linear_lazy`, `internal_linear_lazy`, and `external_local_packed_raw`. The generated terminal path also references iterator construction/reverse-iteration/fold and array mapping in Poseidon evaluation, and `Result.map`/`map_err` in the public wrapper. `manifest.json` records their generated line numbers and stub names. This is a source-based inventory, not a claim that every template line is reachable. The complete remaining reachable stub set is still open.
