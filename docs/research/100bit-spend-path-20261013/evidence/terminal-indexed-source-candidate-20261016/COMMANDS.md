# Prepared command sequence (not executed)

Run only after root/d18 authorizes it on the pinned Linux extraction host. First verify the kit checksums. Then, from the copied kit path, run the prepared preflight and the same isolated release pipeline:

```sh
python3 /path/to/terminal-indexed-loops-candidate-20261016-v3/run_attempt_prepared.py --preflight
python3 /path/to/terminal-indexed-loops-candidate-20261016-v3/run_attempt_prepared.py
```

The runner performs, in order: locked offline `cargo build --release`; Charon from `crate::extraction_probe::terminal_qm31_probe`; and sequential Aeneas Lean extraction. Each command uses the existing user systemd scope with `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`, and a 300-second timeout. Each stage checks reservation state and records source, tool, resource, and output receipts. This file records commands only; no stage has run for v3.
