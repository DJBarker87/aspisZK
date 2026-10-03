# R469: actual R137 Q22 trace bound

R469 proves that the observed, source-shaped R137 Q22 entry for a total oracle `H` appends the Q22 model trace and therefore adds at most 16 decoded calls.  The statement preserves the concrete R137 entry result and returned transcript supplied by R468; it does not turn the observer into a shared oracle or establish a probability law.

The promoted target `lean/AspisV8R19/R469ActualR137Q22TraceBound.lean` is byte-identical to the successful compiler input (SHA-256 `8f399552a0020c1112f17ae6f8c328db7c6b49c6857ec77419855f71e03a09fd`).  It compiled at revision `db69649c51969f5a656c7b824407786356e8af75`, exit 0, in 1.42 s with peak Lean-child RSS 3,703,664 KiB and zero swaps.  Its complete `#print axioms` report is preserved verbatim: `propext`, `Classical.choice`, `Quot.sound`, and `core.fmt.Formatter`; it contains no `sorryAx`.

The earlier attempt is retained as rejected history.  It exited 1 because `omega` did not have the Q22-model bound available and its attempted result reported `sorryAx`; it is not proof evidence.  Both records use `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, and Lean flags `-j1 -M4500`.  GNU time reports Lean-child RSS; the systemd wrapper `MemoryPeak` is not aggregate Lean RSS.

This closes only the R137 Q22-entry trace-size bridge.  It does not prove the whole callback prefix through circles, gamma, kappa, tau, alpha, q22, and rho; shared-oracle behavior; freshness; probability; privacy; or soundness.  The first remaining proposition is the faithful whole-callback trace and state bridge, including all failures and oracle calls.

Run `python3 verify_evidence.py` from `evidence/r469-actual-r137-q22-trace-bound` to validate the saved source, raw run records, complete axiom report, direct imports, runner, and checksum index.  Packaging did not rerun Lean.
