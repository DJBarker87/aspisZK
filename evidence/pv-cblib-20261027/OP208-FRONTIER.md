# V232 / op208: exact source body extracted, compression binding open

Fresh receipts: `charon-source-op208-opt-003` and
`aeneas-source-op208-opt-003`, pinned sha2@0.10.9 core_api.rs, hash in
source-provenance.json. The actual `update_blocks` implementation and its
private two-field core both extract. Generated text is retained as
`op208-Funs.lean.txt` and `op208-Types.lean.txt`.

The generated external-function template still declares
`sha2::sha256::compress256` opaque. No template axiom is compiled. The draft
PV_CBL_Op208Extracted passes this symbol as an explicit `Compression` function
parameter, preserving the complete Result (ok, every error, divergence).
PV_CBL_Op208Shape is labelled a decomposition, not op208_source. This keeps the
missing implementation binding visible rather than relabelling a callback as
a theorem. V232 remains OPEN, with the smaller precise obligation of binding
compress256 to its actual frozen source/intrinsic semantics.

The source arithmetic is wrapping u64 count addition after a usize-to-u64
cast; no checked-arithmetic premise is silently substituted. All state inputs
and block slices remain arbitrary in the draft statement.
