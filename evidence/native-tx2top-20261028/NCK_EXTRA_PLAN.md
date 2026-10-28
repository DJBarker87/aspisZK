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

NCK_L057 had two SSH255 losses before either its source or configuration was
uploaded. A later read-only recovery connection also returned255; the active
run guard correctly refused further launch. Recovery follows60s retries,
never resubmitting an unresolved prover. NCK_build.py now uploads its own
inputs through stdin in a distinct pre-launch transport step, then submits the
unchanged capped S2W launcher separately. This removes large quoted command
arguments and distinguishes upload retry from actual submission. All source,
backend, library, admission and receipt checks remain intact or stricter.
