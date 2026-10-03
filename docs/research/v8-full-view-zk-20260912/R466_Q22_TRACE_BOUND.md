# R466: Q22 source-shaped model trace bound

R466 proves a bound for the source-shaped Q22 model: at most 16 duplex calls and `Within 16`. It does not connect that model trace to the generated R137 Q22 trace or establish shared-oracle behavior, a probability law, or privacy. The first remaining proposition is the actual R137 Q22 trace/source-to-model bridge.

The successful source at `lean/AspisV8R19/R466Q22TraceBound.lean` matches the saved successful compiler input byte-for-byte (SHA-256 `90c5a543d328f5834a6bded8d4abd1e39779d1ef9e871927a56482558f56af35`). It compiled at revision `ca981c001d6df2b76b3126de80b0c2fff5c2fb81`, exit 0, in 1.31 s with peak Lean-child RSS 3,231,396 KiB and zero swaps. The complete four `#print axioms` reports are preserved verbatim in the successful receipt and log; they use `propext`, with `Quot.sound` also reported for the trace and `Within 16` results.

Two earlier R466 attempts are preserved as rejected history. Both exited 1 and reported `sorryAx` on the unfinished trace-bound results; neither is treated as proof evidence. All three attempts record `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, and Lean flags `-j1 -M4500`. GNU time reports Lean-child RSS; systemd wrapper `MemoryPeak` is not aggregate Lean-child RSS.

Run `python3 verify_evidence.py` from the evidence directory to validate the saved source, raw run records, complete axiom reports, direct imports, runner and checksums. No Lean rerun was performed for packaging.
