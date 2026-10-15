# R1 pool-adapter route-guard replay evidence

This bundle records a focused rebuild of the route-guard source overlay and six
local LiteSVM runs against retained split10 proof/public fixtures. It is a
measurement of the selected local S2 fixture path, not a proof of R1 protocol
correctness or security.

## Source and build

The NUC workspace was made by copying the pinned split10 source snapshot,
then overlaying only `programs/r1-cost-probe/src/lib.rs` for the route-guard
entrypoint. The overlay bytes are SHA-256
`36d36ee707f565df675db2ef7b2d27467f8b79bb99142c4b21d6fb7cc81910c9`;
the baseline version of that file is
`294546036e6cf8bb8dcc1f1f4a65c5e0887ac04593cdda801f58c75a284d582a`.
The baseline and overlay manifests each contain 754 paths and differ only at
that file. Commit `3c79ec30fa44f408c716bb345050c137e907fa67` identifies the
lead revision for the route-guard overlay; it does not identify the entire
copied source tree.

The runner checked all 754 copied paths against `source-overlay.sha256`.
A separate comparison against this worktree found 367 current paths in the
scope of root and nested Cargo manifests/locks plus source files under
`crates/`, `programs/`, and `tools/`: 340 are present in the snapshot and
all 340 hashes match. The 27 absent paths are listed in
`results/source-coverage-audit.json`; they are confined to four standalone
tool packages: `tools/r1-hash-input-counter` (3 paths),
`tools/v7-live-pool-proof` (13), `tools/v7-txv1-honest-proof` (4), and
`tools/v8-state-only-cu-probe` (7). Those directories are not members of
the root Cargo workspace. No covered path
has a hash mismatch. The copied snapshot should therefore be read as the
pinned split10 build input plus this one route-guard file, not as a full
snapshot of the current checkout. Build inputs selected features
`pool-adapter,private-leaf-salts`
with `custom-heap`, Solana `cargo-build-sbf` 3.1.13 and platform-tools v1.52
(SBF rustc 1.89.0), `--locked -j 2`, offline, using the retained v1.52 Cargo
target cache. The SBF artifact is
`aspis_r1_cost_probe_program.so`, SHA-256
`243a3193f17744d221706edf835fc71e40de914cde90cbadf9dc74108ba5dd19`.
It is distinct from the adopted split10 ELF (`5a913394...`) and is not marked
adopted here.

The build receipt records cwd `/home/dombarker`; its command names the absolute
pinned manifest under the immutable source snapshot and the runner checks the
source manifests and overlay first. This cwd detail is retained without a
cosmetic rerun. The build used a systemd scope with MemoryHigh 8 GiB,
MemoryMax 10 GiB, MemorySwapMax 0, TasksMax 128. Build exit status was 0,
wall time 1.001 s, sampled aggregate RSS peak 279,945,216 bytes, cgroup memory
peak 123,252,736 bytes, and swap 0.

## Replay results

Each case used the exact proof and public fixture hashes recorded in the case
JSON, the pinned optimized `pool_gate` driver, real TxV0 transactions, and the
same pool/registry binaries as the split10 run. All five non-replay transactions
reported `outcome=accepted`, no execution error, and simulation matching
execution. The repeated transfer-13 case first settled successfully, then its
replay failed with `InstructionError(3, Custom(1095966758))`; the evidence
records the settled state as byte-identical after replay rejection.

| Case | Stage 1 CU | Terminal CU | Split10 baseline stage 1 / terminal | Difference |
| --- | ---: | ---: | ---: | ---: |
| Transfer, 13 pairs | 1,342,855 | 1,286,098 | 1,342,862 / 1,286,105 | -7 / -7 |
| Transfer, 255 pairs | 1,342,604 | 1,352,250 | 1,342,611 / 1,352,257 | -7 / -7 |
| Withdrawal, 255 pairs | 1,341,272 | 1,368,454 | 1,341,279 / 1,368,461 | -7 / -7 |
| Transfer, 1,023 pairs | 1,342,670 | 1,349,205 | 1,342,677 / 1,349,212 | -7 / -7 |
| Withdrawal, 1,023 pairs | 1,341,395 | 1,365,199 | 1,341,402 / 1,365,206 | -7 / -7 |

The transfer-13 run also exercised lifecycle negative cases: tail straddle,
tail injection, wrong authority, repeat initialization, post-seal write,
repeat finalize, malformed candidate finalize, malformed public finalize, and
unsealed stage one. Each recorded the expected rejection and rollback. See the
case evidence JSON for the exact error and state comparison per check.

Per-case resource receipts and outer `/usr/bin/time -v` logs are preserved
beside each run JSON/log. Each used MemoryHigh 8 GiB, MemoryMax 10 GiB,
MemorySwapMax 0, TasksMax 128; each gate exited 0, with about 0.50 s wall time,
roughly 35–36 MB cgroup peak memory, and zero swap. The top-level build and
replay runner scripts, source manifests, SBF build log, all six run logs and
receipts, and generated ASE2/ASR2 fixtures are included. Proof/public fixtures
and generated task keypairs remain outside this repository; no key material is
included in this bundle.

## SBF stack diagnostic follow-up

The successful build receipt is not by itself evidence that the final program
has no over-4-KiB stack accesses: `sbf-build.log` contains 57 stack diagnostic
lines naming 34 functions, including chord, opening, and `point_claims`
functions. A read-only audit used the existing `scripts/r1_p2_stack_audit.py`
method on the matching unstripped v1.52 linked artifact from the pinned Cargo
cache and this bundle's measured ELF. The audit root was adjusted to the
program's actual `entrypoint` symbol (the old script's R1 instruction-handler
name is not present in this route-guard link). The linked and measured `.text`
hashes match. None of the 34 diagnostic symbols appears in the linked ELF;
the conservative entrypoint call-graph closure contains all 276 linked
functions and none of the diagnostic symbols. The final disassembly scan
found 28,194 static `r10`-relative operands: the largest negative offset is
exactly 4,096 bytes and none exceeds 4,096. The largest stack-offset/frame
figures in the build diagnostics (295,552 / 395,456 bytes) belong to symbols
absent from this final linked artifact. Detailed symbol/edge results are in
`results/stack-audit.json`. The exact entrypoint-adapted audit script and the
read-only disassembly scan reproduction recipe are preserved in
`results/stack-audit-route-guard.py`,
`results/scan-r10-stack-operands.py`, and
`results/stack-audit-reproduction.sh`. The scanned unstripped disassembly
captured on the NUC had SHA-256
`68534c2269b8bb64165f79ceed2dd4da40c95e7285237e8f9d5b8dc26e562d7b`;
the reproduction recipe recreates it in a fresh scratch directory from the
pinned linked artifact. This is an ELF-specific static audit, not a claim about
other builds or runtime stack behavior beyond the linked SBF code.

## Limits

These are deterministic local LiteSVM measurements with explicit fixture reuse.
They do not establish proof soundness, source/compiler refinement, mainnet
behavior, or a security claim. The -7 CU differences are observed for these
matched fixtures and this build only.
