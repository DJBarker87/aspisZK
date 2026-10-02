# R425 saved integration-run audit

PASS — Saved R425 InterpExpressions integration compilation only; no build/test/translation rerun.

The isolated release-profile Dune target completed with exit status 0; GNU time records 12.71 s wall, 395416 KiB peak RSS, and zero swaps. The command and Docker records show a 5 GiB reservation, 7 GiB memory limit, equal memory-swap setting (no added container swap), 128 PID limit, no network, and the `aspisr425.slice` parent; the host systemd slice records `MemorySwapMax=0`. All three source snapshots match reviewed inputs, and the helper predecessor is recorded green. Axiom reporting is not applicable to this OCaml compile. This establishes integration typechecking only; it records no fixture execution, translation, or Lean proof.
