# D LLBC Aeneas retry with `-loops-no-rec`

This separate Aeneas-only configuration check uses the unchanged D LLBC and merged source manifest; Cargo and Charon were not rerun. Aeneas exited 2 after 2.08 seconds. `/usr/bin/time -v` reported maximum RSS 223,168 KiB and zero swaps. The command used a systemd user scope with `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and `TasksMax=128`.

The failure is identical to the D default and `-loops-to-rec` attempts: reachable `src/statement/state_only_poseidon.rs:156:8–172:9`, `Unimplemented` from `interp/InterpMatchCtxs.ml:419` while joining shared and mutable loans. No Lean declarations were emitted. Input LLBC SHA-256: `9f759f9eef92afd1439d8fa8639bf629f86ef8ac94548beab9d7a84aac01af33`; source manifest SHA-256: `f0b0adafafbfa4722946a656e8d3f91e50be872e2a607d4c6e1e20097f9a3534`; Aeneas SHA-256: `959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3`.
