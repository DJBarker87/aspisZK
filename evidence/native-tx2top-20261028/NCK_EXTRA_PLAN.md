# Native attempt preparation notes

NCK_K001 compiled optimized frozen dependencies, then failed because my
scratch input omitted tools/r1-builder-reference/tree.rs. This is an own-input
failure, not a timeout or infrastructure error. The frozen directory was added;
its files are now in NCK_FROZEN_MANIFEST.json. NCK_K002 is the corrected gate.
The earlier metadata-only failure omitted c3/build; it launched no proof and is
not a Kani run. Scratch Cargo.lock remained frozen. No library/source body
was changed to fix either missing-input error.

KMX_copy_stubs.patch is applied exactly, SHA256
bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
The first submitted property is its matching deliberately false pointer-copy
control; no copy-dependent positive receives credit before that control fails.

NCK_kani.py's own transport log now stores large stdout losslessly in .xz,
with uncompressed sha256/length instead of duplicating cargo-metadata JSON
inside every transport line. Parsing and graph validation still use the full
original stdout. This changes storage only. Shared launchers are unchanged.
