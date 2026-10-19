# D LLBC Aeneas retry with `-loops-to-rec`

This is an Aeneas-only retry using the unchanged D LLBC and merged source manifest. The sole translator-option change from D's Aeneas invocation is `-loops-to-rec`; Cargo and Charon were not rerun.

The LLBC SHA-256 is `9f759f9eef92afd1439d8fa8639bf629f86ef8ac94548beab9d7a84aac01af33`; merged source manifest SHA-256 is `f0b0adafafbfa4722946a656e8d3f91e50be872e2a607d4c6e1e20097f9a3534`. Aeneas executable SHA-256 is `959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3`.

The executed retry exited 2 after 2.08 seconds. `/usr/bin/time -v` reported maximum RSS 222,992 KiB and zero swaps. It ran under a systemd user scope with `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and `TasksMax=128`. Translation again stopped at reachable `src/statement/state_only_poseidon.rs:156:8–172:9`, reported as `Unimplemented` from `interp/InterpMatchCtxs.ml:419` while joining shared and mutable loans. No Lean output was emitted.

The first launcher invocation in this directory did not start Aeneas: systemd rejected the unsupported combination `--wait --scope`. Its stderr/time log is retained separately as `receipts/aeneas.stderr.log`. The executed retry is `receipts/aeneas-b.*`; its command is also recorded in `receipts/aeneas-command.txt`. Both attempts used the unchanged LLBC and manifest copies in `input/`.
