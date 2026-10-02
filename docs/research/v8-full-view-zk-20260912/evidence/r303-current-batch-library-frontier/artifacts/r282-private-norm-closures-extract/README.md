# R282 isolated private norm-closure extraction (prepared only)

This directory contains a prepared runner for one pinned, optimized Charon extraction rooted at:

`crate::circle_norm::joined_inverse::line_norm::r110_norm::try_norm::_::call_once`

The wildcard is intentionally one path element, matching the three closure implementation nodes identified in the saved R280 output. The extraction is isolated from R280's batch/try_norm roots and R266's B negation/inversion roots. R280 metadata shows the relevant local `call_once` names under `try_norm` as `ImplTrait20`, `ImplTrait22`, and `ImplTrait24`; their companion `call_mut` methods were numbered 21, 23, and 25 in that output. The source spans correspond to the `norms_m` map, output reconstruction map, and base-inverse conversion map. These are preparation observations, not asserted extraction results for R282.

After Charon succeeds, the runner reads the emitted LLBC JSON without rewriting it and asserts exactly three `try_norm`-local `call_once` function declarations and three corresponding `call_mut` declarations. It saves each declaration's path, source text, span, signature, and generic metadata to `closure-counts.json`; actual counts are asserted only after extraction. The assertion checks metadata inventory, not source semantics.

The runner reuses the R266 frozen source hashes, Charon `aeneas` preset, built MIR, default sysroot, `core::option` and `aspis_core::field` includes, disabled monomorphization, `--offline --locked --release --jobs 1`, feature set `insecure-spend-fixture,selected-v7-kernels`, and saved optimized Rust flags SHA-256 `f2485133cd857d119d387fcddda1a7fe2607e04dbec4756adbaacd3e765363613`. It records launch revision `380c7d46c9719dcfcab601fac2607861d47dee02`; the frozen source snapshot has no Git metadata, so the seven exact source/manifest/lock hashes are checked before execution.

The proposed dedicated systemd scope is `aspis-r282-private-norm-closures-extract`, with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. The unique proposed remote output root is `/home/dombarker/project-offloads/aspis-r282-private-norm-closures-extract-20261002-a`. Expected work is cached optimized Charon extraction only. No extraction or host command has been launched while preparing this runner; launch awaits the R281 job and lead review.
