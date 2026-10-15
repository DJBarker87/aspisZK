# J1 public serializer: source-extraction reuse inventory

This is a source/tooling inventory at repository revision `764bf20a6fe0392951b670f73748a54f70c9f272`. It records reusable pieces and prior extraction behavior; it does not establish a Lean refinement of the current `Public::public_bytes` implementation.

## Current serializer and required input cone

The current method is `r0::Public::public_bytes` in [`pair_forest_semantic_terminal.rs`](../../../../crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:2002), SHA-256 `2bb7db64dc53c8a268e42b0fe46da64ab1afcb03d28bbec2569b2abc30cbc074`. It first calls `self.semantic()` (lines 1989–1995), which dispatches to `private_public` and `withdrawal_public` (lines 1312–1345). A source extraction rooted at `public_bytes` therefore needs those definitions and the referenced `SemanticPublic`, variant, `M31`, `Digest`, and transition/frontier types. It reads `transition.live_snapshot.next_pair_index`, `live_snapshot.frontier`, `candidate_afterstate.next_root`, and `candidate_afterstate.next_frontier`.

The body uses `Vec::new`, `Vec::push`, and `Vec::extend_from_slice`. Its nested `fields` helper checks each `M31.0 < P`, then appends `value.0.to_le_bytes()` (lines 2003–2011). The variant byte is 0/1 (2014–2017); optional recipient and amount are each preceded by a presence byte (2022–2029); the source pair index is appended as eight little-endian bytes (2032); then the two frontiers and next root are appended (2033–2038). Pool/domain and the old current root are not serialized, as the method's comment states (1999–2001).

For an isolated extraction probe, the minimum useful entry is the unchanged `Public::public_bytes` method, not a copied serializer shim. Its transitive source cone must include its `semantic` conversion functions and the actual field/transition type definitions. If extraction reachability needs to be reduced further, the caller should preserve this method body and its exact inputs while pruning unrelated terminal code; a separately written helper would need its own source-equality argument. This note does not assert that such extraction has been run.

## Reusable Aeneas and Lean pieces

The retained Aeneas Vec source is [`Vec.lean`](../../../../docs/research/v8-full-view-zk-20260912/evidence/r319-current-batch-prefix-step-execution/library-source-preflight/Vec.lean), SHA-256 `ebe737c37f7e0ca074b3de4edeaa2fba826952f7377d01317699e8e4e7b65f87` (the r306 copy has the same hash). It defines `alloc.vec.Vec` as a bounded list, `Vec.new` as empty, `Vec.push` as a fallible append with `Vec.push_spec`, and `alloc.vec.Vec.extend_from_slice` at lines 352–363. The latter clones the slice and appends its list contents when the Usize bound holds. Thus a generic Vec/list model exists in retained library source. The old executable Lean modules [`AspisR318BatchPrefixRaw.lean`](../../../../docs/research/v8-full-view-zk-20260912/lean/AspisR318BatchPrefixRaw.lean:19) and `AspisR86Query/Loops.lean` use translated `Vec.push`/`Vec.deref`; they do not prove this current serializer or a `Vec::extend_from_slice` call chain.

The retained generated field module [`AspisR137Transcript/Funs.lean`](../../../../docs/research/v8-full-view-zk-20260912/lean/AspisR137Transcript/Funs.lean:36), SHA-256 `606f3dc4f140389e0a48fd173979f2fe6529dc151f7f839f04e81f5022969124`, has `field.M31.to_le_bytes : field.M31 → Result (Array U8 4)` delegating to `core.num.U32.to_le_bytes`, plus `CM31.write_le_bytes` and `QM31.write_le_bytes` using slice writes (lines 53–117). This is a previous translated API for fixed-size field serialization, not a retained declaration proving current `u32::to_le_bytes` or the public serializer's `Vec` accumulation. The full Aeneas Vec source also contains the annotated standard-library `extend_from_slice` binding, but there is no retained generated theorem applying it to this public method.

The current isolated parser extraction runner [`extract-field-parsers.py`](../../../../docs/research/100bit-spend-path-20261013/tools/extract-field-parsers.py), SHA-256 `3dccc0ea2c6ea0c4d5c40ef836aed287672bd64b59d8d87f1d8ab7d7c006841e`, pins Charon and Aeneas, copies exact pinned input sources, builds offline in release mode, and runs Charon from a selected entry (`--start-from`, default `crate::parse_fields_probe`) before Aeneas translation. Its minimal crate exports field parser probes over fixed arrays. It uses `--include core::option` and `--include core::result`. Prior attempts retained under `evidence/field-parser-extraction-*` show Charon succeeding while Aeneas failed on a `Result::ok` match (`Inconsistent state`, `core/result.rs:713–717`) for the attempted parser route; the resulting artifacts do not establish that Vec operations are unsupported. Conversely, no retained attempt here translates `Public::public_bytes`, `Vec::extend_from_slice`, or its local `fields` helper.

## Current mathematical codecs

The current tree already contains independent model codecs:

- [`RetainedFieldByteCodec.lean`](../../../../docs/research/100bit-spend-path-20261013/lean/RetainedFieldByteCodec.lean) models four-byte little-endian words and M31/QM31 byte lists.
- [`AeneasWordCodec.lean`](../../../../docs/research/100bit-spend-path-20261013/lean/AeneasWordCodec.lean) proves `aeneasWord_val_eq`, equating an extracted Aeneas U32 decoder's value with the retained word codec for four bytes.
- [`PublicIndexCodec.lean`](../../../../docs/research/100bit-spend-path-20261013/lean/PublicIndexCodec.lean), SHA-256 `2ea8f5606b7b083b6032ee850709f825792726b29ff39ab0e8418e1a2b111645`, proves `decode_encode`, `encode_decode`, and `decode_val` for an abstract `Fin (2^64)` index represented as eight bytes split into low/high 32-bit words. [`PublicIndexListCodec.lean`](../../../../docs/research/100bit-spend-path-20261013/lean/PublicIndexListCodec.lean), SHA-256 `122cda762fc4268fc30f20cbff666346c347e3c725294be997f602eeeebf5058`, adds exact list length 8 and fixed-width list roundtrips.
- [`SemanticPublicWire.lean`](../../../../docs/research/100bit-spend-path-20261013/lean/SemanticPublicWire.lean), SHA-256 `cfc7a99fb041e9a7d2ad56d2fb5e02c1c18a4c8976c70e22af0672909a4b247a`, defines the mathematical variant/wire encoding and parser; `SemanticPublicWireRoundTrip` proves model roundtrip and `SemanticPublicByteBinding` proves byte reconstruction from successful model parsing.

These codecs establish properties of their Lean definitions. They do not currently connect the Rust `Public::public_bytes` body to `SemanticPublicWire.encode`, and the standalone parser extraction does not fill that gap. A proof of that connection would need to account for the actual enum-to-`SemanticPublic` conversion, field canonicality rejection, exact `Vec` append behavior, little-endian encodings, and the source method's field ordering.

## Pins

| Item | SHA-256 |
|---|---|
| Current serializer source | `2bb7db64dc53c8a268e42b0fe46da64ab1afcb03d28bbec2569b2abc30cbc074` |
| Parser extraction runner | `3dccc0ea2c6ea0c4d5c40ef836aed287672bd64b59d8d87f1d8ab7d7c006841e` |
| Retained Aeneas Vec model | `ebe737c37f7e0ca074b3de4edeaa2fba826952f7377d01317699e8e4e7b65f87` |
| Retained Aeneas field generated module | `606f3dc4f140389e0a48fd173979f2fe6529dc151f7f839f04e81f5022969124` |
| Current Aeneas U32 word bridge | `be850b08a8ee72dd28001c521a5af21b251fc4d8c899069388809880f03a770b` |
| Current public index codec | `2ea8f5606b7b083b6032ee850709f825792726b29ff39ab0e8418e1a2b111645` |
| Current public index list codec | `122cda762fc4268fc30f20cbff666346c347e3c725294be997f602eeeebf5058` |
| Current semantic public wire model | `cfc7a99fb041e9a7d2ad56d2fb5e02c1c18a4c8976c70e22af0672909a4b247a` |
