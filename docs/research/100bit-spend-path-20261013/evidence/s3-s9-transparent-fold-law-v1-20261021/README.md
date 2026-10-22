# Transparent Rust `Iterator::fold` and scalar-factor consumer

This packet pins the full-MIR extraction of Rust core `Iterator::fold`, the exact three-definition generated Lean cut, a strong-induction proof against the selected P6 range model, and the actual scalar-factor polynomial consumer with the fold premise derived.

The proof is source-derived for Charon/Aeneas LLBC and has standard Lean axioms only. It does not close the separate P6 correspondence between the selected Aeneas Std `RangeIter`/`from_fn` models and Rust `std`, nor the outer `Weights::pair` caller. The polynomial consumer still takes the actual scalar-factor success/output, `kpowers` success, canonical inputs/seed, and zero canonical/decode facts as premises.

The Rust nightly sysroot source is included with its full SHA-256 and toolchain pin. Charon's exact command intentionally omitted `--sysroot default` rather than passing a path; `RUSTUP_TOOLCHAIN=nightly-2026-06-01` selected the installed full-MIR toolchain.

No Lean `.olean` binaries are included. Their hashes and producing receipts are recorded in `manifest.json`; the objects remained in the local warm cache at `/tmp/transparent-fold-v1-local/objects`.

Run `python3 check_packet.py` from this directory to verify source, generated-cut, LLBC, and manifest hashes.
