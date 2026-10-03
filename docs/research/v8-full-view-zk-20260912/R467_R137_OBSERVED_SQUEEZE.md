# R467: R137 observed squeeze and query adapter

R467 proves that one R86 observed squeeze erases exactly to the actual R137 squeeze under `toR137`. It also proves the total query adapter records exactly two calls and decodes the trace. This does not establish the whole Q22-loop actual trace, shared-oracle probability, privacy, or soundness. The first remaining proposition is the bridge for the complete Q22-loop actual trace.

The successful target `AspisV8R19/R467R137ObservedSqueeze.lean` matches the saved successful input byte-for-byte (SHA-256 `bf93b704348651451ebdd3d844b11b438f01629105b33fc00309a6ad5a85a057`). It compiled at revision `3e0ade53ee75ab71e00cec853b984deb01542958`, exit 0, wall 1.61 s, peak Lean-child RSS 3,703,652 KiB, swap 0. The complete four `#print axioms` outputs are preserved in the successful receipt and raw log; each lists `propext`, `Classical.choice`, and `Quot.sound`.

Six earlier attempts are preserved as failed history with their original source, command, receipt, and log. They exited 1 and their axiom output includes `sorryAx` on at least one attempted result; none is treated as proof evidence. All recorded runs use `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, and Lean flags `-j1 -M4500`. GNU time records Lean-child RSS; the systemd wrapper's `MemoryPeak` is not aggregate Lean RSS.

Run `python3 verify_evidence.py` from the evidence directory to check source identity, all seven run records, full axiom output, direct imports, runner, and checksums. Packaging did not rerun Lean.
