# R295 focused translation of R294 batch extraction

This is one sequential Aeneas translation attempt over the exact unchanged R294 LLBC, using the original pinned Aeneas binary from R292. It retains the original Charon `ordered_decls`; no metadata reordering or template edits are performed. The destination namespace is `AspisR295PrivateBatch`.

Input gate: R294 LLBC SHA-256 `bf5ea0b6f68ab17ef73d3e721c70c9193a0682d95dcbcaf693e93187cf71da6f`, `has_errors=false`, root Fun0 is local with a non-opaque body, and its original ordering contains `Fun NonRec 0` (the runner records the actual index). Aeneas binary SHA-256 is expected to be `63b04a88532b8fb0aaa0d274881b5cacf00bc4f449243ece905178f0de9cc495`.

The run uses sequential, abort-on-error, Lean backend, split files, and JSON manifest output in an isolated 5 GiB high / 7 GiB max / zero-swap / 128-task systemd scope. The runner records exact source revision at launch, hashes, resource reservations, translator exit, root manifest and emitted `def` line, output hashes, warnings, and unresolved external templates. It does not fill templates, compile Lean, or make proof or source-correspondence claims. Any generated holes remain obligations.

## Observed result

Aeneas imported the pinned R294 LLBC, then exited 2 before creating a generated directory or `translation.json`. It raised an internal error at the pinned Rust standard-library span `core/src/iter/traits/iterator.rs:2486:4–2490:35`, in Aeneas `symbolic/SymbolicToPureTypes.ml:1047` while translating function signatures. The complete stack trace and GNU time output are in `translate.log`; `translation-result.json` records that no root manifest entry or Lean definition was emitted. Since translation stopped before output emission, there are no generated helpers or template holes to inventory from R295.

GNU time reports wall 0.25 s, peak RSS 70,224 KiB, swaps 0, exit status 2. The systemd unit completed with status 2 and reported a 390 ms service runtime, zero swap, and its recorded memory peak in `launch.log`. Preflight and after-run reservations are retained. No retry, template fill, Lean compile, or semantic conclusion was made.
