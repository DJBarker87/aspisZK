# R398 generic batch translation attempt

R398 attempted to translate the complete, unchanged R396 LLBC with the pinned R385 v2 Aeneas binary and its reviewed sequential Lean backend flags. The input SHA256 is `399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae`; the translator binary SHA256 is `f12977c5acd368d268d3af9562110ab29be60d7b4055dde937d0049f85409db5`. The run used a fresh output root and a 5 GiB high / 7 GiB max / zero-swap / 128-task systemd scope.

The translator exited 2 before producing a generated directory. Its first diagnostic is an internal error on `/rustc/library/core/src/iter/traits/iterator.rs:2486:4–2490:35` at `symbolic/SymbolicToPureTypes.ml:1047`, raised by `sanity_check_opt_span` while translating function signatures. The process took 0.23 seconds, reached 71,280 KiB maximum RSS, and used zero swaps. The exact remote command, payload, full log, reservation snapshots, output result, and launch receipt are retained below.

`audit_r398.py` validates the saved receipts/logs and checks the input and binary hashes. No retry, LLBC edit, template filling, Lean compilation, or source-semantics/security claim is included. `#print axioms` is not applicable because no Lean target was produced.
