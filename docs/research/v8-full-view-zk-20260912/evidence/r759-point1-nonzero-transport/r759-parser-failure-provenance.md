# R759 parser-failure source provenance

`r759-generator-run.log` is the first R759 attempt. It used the renamed,
pre-parser-fix emitter reconstructed byte-for-byte as
`r759-transport-emitter-pre-parser-fix.rs`.

Its SHA-256 must be `14883afab8a82d4b2fcc127d00ca936508be7c9fc8dda73c50a954e5ef460c67`.
The failure occurred after optimized Rust compilation, when parsing a generated
basis declaration; no transport output was emitted. The subsequent source only
replaced that parser with whitespace-token parsing and diagnostic labels.
