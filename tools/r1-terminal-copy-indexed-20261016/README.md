# Isolated terminal Copy-helper/indexed-fold candidate

This worktree starts from commit `a8930e677bc745854b9f693b5628c8a8bd2ac848` in the proof worktree. The three candidate source files are isolated working-tree edits; no build, differential, SBF build, or runtime replay has been run here.

`prepare.py` preserves the committed three-file source snapshot under `base/`, checks the input revision and hashes on repeat runs, regenerates `candidate/`, the patches, and `source-pin-manifest.json`, and overlays only those candidate files into the worktree. It changes:

- `lib.rs`: adds `array_from_fn_copy<T: Copy, const N>` that initializes `[init; N]`, then calls `FnMut` in increasing index order.
- `state_only_poseidon.rs`: carries forward the already reviewed external-row helper lift, transforms the 10 selected `from_fn` call sites in that file, and uses four explicit row writes from the pre-write copied input.
- `pool_v1/pair_forest_semantic_terminal.rs`: transforms the 8 selected `from_fn` call sites and replaces two owning reverse-array loops by reverse-index loops, keeping multiply/add order and indices 23→0 then 3→0.

The manifest pins all baseline and candidate source hashes, the current `r18_replay.rs` and Cargo inputs, and the retained transfer-1023 proof/public inputs. `compare-checkpoints.py` is post-run instrumentation only: given an `r18_replay` output directory, it verifies the driver's admitted 3-account/7-account stages, unchanged inputs, 1768-byte checkpoint equality, and 792-byte ASR8 equality, then emits hashes. It never launches transactions or reads key contents.

The latest retained R18 and terminal-validator receipts show the current 3/7 account route succeeds on the saved transfer-1023 fixture, with checkpoint and output bytes equal in their respective before/after comparisons. Those receipts are explicitly prior-reference evidence and do not measure this candidate. The fixed fixture is 124343-byte proof SHA `856943…9d62` and 1880-byte public SHA `72f067…2172`.

This candidate remains an experiment. Its repeated initialization writes, generated code size, CU, stack, and source correspondence have not been measured or established. No key material is included or altered.
