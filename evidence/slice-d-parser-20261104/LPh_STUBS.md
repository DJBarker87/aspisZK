# NGD field-callee stub table

| Scratch stub | Paired named Lean law | Domain established by caller | Status |
|---|---|---|---|
| NGD_wire::NGD_decode_le for QM31::from_le_bytes | NGD_QDecodeLaw.stub_law, application of the retained ActualDecodeKStrictQM31Parser.source_refines | SAME original low-16 window, length exactly 16; all bytes, including noncanonical four-word encodings. No canonical-input assumption. | Compiled L027 and re-imported L067; K036/37, K043/44, K096–K099 pass/control. Full natural Rust-stub/codec association remains OPEN for composed caller credit. |

The stub returns four natural little-endian words in coordinate order (c0.a,c0.b,c1.a,c1.b) iff every word is < 2147483647, otherwise None. The retained codec decodeQM31LE uses precisely that predicate/word encoding; the full byte/code natural association is an explicit pending check, never inferred from a theorem name. The law concerns the actual emitted decoder and exact returned value/error. No multiplication is evaluated or stubbed. Opaque-Q native source/compiler/library realization remains the cited child bridge, not a new cryptographic assumption. K035 actual-body timeout remains excluded and is never rerun unchanged.

NGD_DecodeValueLaw.value (L058) identifies the SAME original low-16 input and exact codec/error index in the emitted helper. NGD_DecodeTrace.step/loop (L065) and NGD_DecodeEntry.ready (L066) transport it through emitted steps. This does not assert the Rust stub equals that natural codec under P6, or construct the native/model finite trace; those remain explicit obligations.
