# Combined R1 freeze — 20 October 2026

Status: **PASS — combined-source R1 artifact frozen.**
Source: `b2727acd3abf79315d18b754a260f58f4b1c6326`, branch
`codex/cx-pin-20261020`. No verifier source changes are made by this task.
Host workspace: `/home/dombarker/project-offloads/codex-cx-pin-20261020`.

The combined source contains both the deployment-ID slots and stage-2 refactor.
Earlier independent gate runs do not establish this combined artifact.

## Artifact identity

The same-source default/devnet comparison passes: `.text` is byte-identical,
section tables are equal, and substituting the two 32-byte ID slots reconstructs
the complete devnet ELF. Pool: `.rodata` offset 0, file offset 1,470,512.
Registry: `.rodata` offset 32, file offset 1,470,544. There are 63 differing bytes,
all inside those slots. The remaining byte happens to be equal.

## Execution policy

Every executable gate uses its own systemd scope with MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0 and TasksMax=64. Native Rust uses release mode,
`-j 4` and `RUSTFLAGS='-C link-arg=-Wl,--threads=4'`. Charon follows the pinned
single-job extraction command. The SBF build passes the equivalent direct-lld
`--threads=4` spelling through target-specific flags, removing the cc-wrapper
spelling for cargo-build-sbf. All binaries and LLBC remain on the build host.
No Lean compilation or new theorem is part of this Rust/SBF task;
`#print axioms` is not applicable.

Three metadata-only setup attempts failed before compilation while the initial
host source copy lacked transitive workspace/path dependencies. They are retained
under receipts/setup-incomplete*. A receipt-wrapper indexing error stopped one
identity attempt before executing the comparison; `setup-attempts.json`
records the wrapper error. The wrapper was fixed before the successful gate.
No failed source gate was retried or resource cap raised.

## Stage-2 extraction

Pinned Charon and Aeneas both succeed, with `has_errors=false`. Raw LLBC:
`f11e40b4119578eee1ebef90874f436dc35b1076f6db27baaa92a79c0919538d`
(7,009,202 bytes). This is **not** the prior `41b2dd71b` evidence hash
`4c36344e1de0f90dfa074fc35a0664408b4f258a11c72617d7a0241fd6aa3182`.
The JSON objects become exactly equal after replacing only
`translated.options.dest_file` with a common value and sorting the
`translated.short_names` map entries by key. Every other JSON value, including
the concrete function bodies, is identical. Canonical JSON SHA-256:
`2acb9b64406eb382e6c9f95dcf0209b6e88d11a1ce8d5f469c73f8a2273a5630`.
See `llbc-comparison.json` and the pinned extraction commands. This establishes
successful emission of the existing cone, not a backend-complete proof.

## Six-fixture CU gate

All six accept using the rebuilt default ELF. Margins are `B1 - stage1` and
`B1 + 10,000 - settlement`; all are nonnegative.

| Fixture | Stage 1 CU | B1 stage 1 | Margin | Settlement CU | B1 settlement | Margin |
|---|---:|---:|---:|---:|---:|---:|
| transfer-13 | 1197177 | 1199648 | 2471 | 1138518 | 1129757 | 1239 |
| transfer-255 | 1199286 | 1199567 | 281 | 1169558 | 1161066 | 1508 |
| transfer-1023 | 1193428 | 1199687 | 6259 | 1169306 | 1160974 | 1668 |
| withdrawal-13 | 1193569 | 1198225 | 4656 | 1148816 | 1138950 | 134 |
| withdrawal-255 | 1193699 | 1198264 | 4565 | 1178769 | 1170523 | 1754 |
| withdrawal-1023 | 1195178 | 1198386 | 3208 | 1176341 | 1170263 | 3922 |

These fixture measurements do not establish an all-input CU bound.

## Standing gates

Passed: codec 1,233 byte-identical; ordered adopted/audit traces
(1,095/583 calls) equal the pinned baselines; program 34/34, including
checkpoint tests; default/detail/audit crate tests and integrations; Pool
87/118/123/123 unit tests for default/R1/all/v7 features, each with two
integration tests; strict default/devnet linked-ELF stack audits; proof-size
teeth; authenticated tx2; masked transfer and withdrawal fixtures.

The executable hashes, exact commands, source revision, wall time, peak RSS,
swaps and cgroup limits are in the receipts. Large codec and Aeneas debug logs
are represented by SHA-256/byte-count pins; complete originals remain at the
recorded host paths. No binary artifacts are committed.

## Executable pins

| Artifact | SHA-256 | Bytes |
|---|---|---:|
| Default verifier | `dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34` | 1,507,400 |
| Devnet verifier | `fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78` | 1,507,400 |
| Pool | `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` | 605,704 |
| Registry | `7ad46f0d4b102a7c9699149d23bf6e065b6151feeaca95977d0a3146167d01ab` | 209,280 |

`artifacts-sha256.txt` also pins both unstripped verifier ELFs, the unstripped
Pool ELF, LLBC and the retained fixture driver. `source-hashes.json` enumerates
every tracked file in the verifier library and program crates, plus workspace
Cargo inputs. `charon-input.json` and `aeneas-input.json` pin translator binaries,
frontiers, transparent layouts, commands and source inputs.

Native Rust/Cargo: 1.94.1. SBF: cargo-build-sbf 3.1.13, platform-tools v1.52,
Rust 1.89.0-dev, LLVM 20.1.7. Charon compilation: nightly-2026-06-01,
Rust 1.98.0-nightly (`14210df0e`). Full versions: `toolchains.txt`.

## Final acceptance

All requested gates pass on the combined source. P_R1 accepts 8/8 and verifies
all eight with strict tx1+tx2 and dense; its separate retry loop accepts in one
attempt and verifies. Gate: 348.766 s, 602,376 KiB peak RSS, zero swaps.
The prover/simulator unit suite passes 33/33, none ignored (329.079 s,
571,420 KiB peak RSS, zero swaps), including all four `sim.rs` tests.

Four timed D78 simulations pass strict tx1+tx2 and dense under the programmed
oracle, reject under the real hash and read every programmed address. All
accept on the first draw; generation takes 34.393–34.669 s. Results are in
`simulator.json`. The 28 proof-size mutations reject, and the authenticated
trace/checkpoint mutation checks pass. Thirteen separate runtime scenarios
cover replay/double-spend (ordinary and prefunded markers), rent-prefunded
success, wrong release, stale lane, proof rejection and withdrawal CPI
failure; complete driver assertions and JSON evidence are retained. The six
ordinary success fixtures are not rerun as part of those scenarios.

Pool was rebuilt from this source: exact expected SHA-256, 28.409 s,
644,840 KiB peak RSS, zero swaps. Its strict complete-linked-ELF audit passes.
All three strict audits have no surviving oversized frame, overwrite or
unparsed diagnostic. Compiler diagnostics for dead legacy functions are
classified against full linked symbols and relocations, not ignored by name.

`runs.json` indexes 44 successful capped command receipts. Default/devnet SBF
builds have two additional complete receipts under `receipts/build-*`.
`validation.json` records the final read-only assertions, including artifact
identity, source hashes, codec/trace equality, CU limits, retry results,
simulator results, Pool identity and stack audits. All executed source gates
exit zero and use zero swaps. Setup-only failures are separately disclosed
above; no source gate failed or was retried.

This pin supplies measured artifact correspondence for the frozen R1 verifier.
It does not discharge the inherited source/model/backend refinement premises,
a universal soundness theorem, or an all-input CU bound. No deployment or
network transaction was performed. Build-generated keys remain on the host;
no wallet/account key cleanup was performed.

Raw command/compiler/test receipts preserve their original whitespace;
`git diff --check` consequently reports padding and final blank lines in those
logs. No source file is changed, and authored harness syntax checks pass.
