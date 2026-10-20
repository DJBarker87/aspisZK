# R1 public devnet resumption — 20 October 2026

Status: **BLOCKED at the required release identity gate; NO-GO**. The payer
is funded with **5 SOL**. No deployment, account initialization, proof upload,
or spend was submitted. The data-only premise in the lead decision is false
for the frozen ELF: its deployment IDs are SBF instruction immediates.

Branch: `codex/cx-devnet2-20261020`; implementation revision `30eb0519a`;
base `0c614b660`. Host task directory:
`dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-devnet-20261020`.
The earlier blocked attempt remains in commits `4529498e6`, `8f416fb72`
and the original receipts. This report supersedes its zero-balance status.

## Stage 1 — deployment constants and frozen/default reproduction

`programs/r1-cost-probe/src/deployment_ids.rs` decodes base58 addresses at
compile time through `option_env!`. The two constants in `r1_pool_adapter.rs`
use `ASPIS_R1_POOL_PROGRAM_ID` and `ASPIS_R1_REGISTRY_PROGRAM_ID`;
unset variables retain `[0x41;32]` and `[0x44;32]`. Empty, invalid, overflowing,
or wrong-length addresses fail compilation. There is no runtime ID decoder,
no dependency or lockfile change, and no change to admitted routes.
Source inspection found no additional deployment-specific program ID on these
routes; policy binding `[7;32]`, profile/release bindings and builtin program
IDs remain as before.

The final default rebuild is **byte-identical to the frozen ELF**, including
`.text`: SHA-256 `8cf8d84ed0fe340a190b4f40a9f953f0e0523370299ba3ec8bbed9d65b88ace3`,
1,405,680 bytes; whole-file and extracted-text `cmp` both exit 0.
`receipts/build-default/` records the command, environment, revision,
resource limits, exit, time and hash. `receipts/default-compare/` records the
`llvm-objdump -h` section inventories and `cmp` results.

## Stage 1 — devnet candidate: identity gate FAILED

The env-supplied build uses the reserved Pool/registry IDs below and compiles
successfully. Its SHA-256 is
`a28ce7fd087570b7de3535d07de8c92dec0364197b9fb36c54db28c6632fbf5a`.
This is a **rejected candidate**, not an admitted devnet release.

| Measurement | Frozen/default | Devnet candidate |
| --- | ---: | ---: |
| ELF bytes | 1,405,680 | 1,405,904 |
| `.text` bytes | 1,368,616 | 1,368,792 |
| `.rodata` bytes | 20,560 | 20,592 |
| `.data.rel.ro` bytes | 4,832 | 4,832 |
| `.text` file offset | 288 (`0x120`) | 288 (`0x120`) |

Extracted `.text` `cmp` exits **1**, first difference at section byte **101**
(1-based). The Rust byte audit exits **1**: section tables differ, 646,260
bytes differ over the common file extent, and **zero** contiguous 32-byte
occurrences of either placeholder exist anywhere in the frozen ELF. There
are no two 32-byte `.rodata`/`.data` offsets that satisfy the requested patch.
The ELF has no plain `.data` section.

`llvm-objdump -d` exposes these frozen instruction/file offsets (hex):

| ID | `lddw` instruction offsets in frozen `.text` |
| --- | --- |
| Pool `0x4141414141414141` | `0x1b9f0`, `0x1ba20`, `0x20ac0`, `0x20af0` |
| Registry `0x4444444444444444` | `0x1baa0`, `0x1bad0`, `0x1bc50`, `0x1ced8`, `0x1cf08` |

Each 64-bit immediate occupies two four-byte fields at instruction offset
`+4` and `+12`. For example, instructions at `0x20ac0` and `0x20af0` load
Pool placeholder words; subsequent comparisons check all four words of the
request's Pool ID. Keeping those instruction bytes fixes the authenticated
ID to the audit placeholder. A data-only substitution cannot change it.

Evidence: `receipts/deployment-identity/` (section inventories, `cmp`,
instruction excerpts), `receipts/final-native-checks/audit.*` (final Rust
byte comparison), and [artifacts-sha256.txt](artifacts-sha256.txt).
The binding common rule says to stop an item whose target is false and
record the obstruction. Therefore the candidate is retained but not deployed;
the old CU bound is **not** claimed to carry over through `.text` identity.
The lead must revise the data-only requirement before this deployment can
be admitted and measured. No broader on-chain logic change was made here.

## Stage 1 — build attempts, validation and resources

All compilation ran on the host in capped scopes: `MemoryHigh=6G`,
`MemoryMax=8G`, `MemorySwapMax=0`, `TasksMax=64`; optimized SBF/native,
`-j 4` for Cargo. The populated reservation observed before the first build
was three 8-GiB worker scopes plus this task's 8-GiB funding watcher; one
8-GiB build scope brought the total to 40 GiB, below the 55-GiB limit.
No other worker was modified or stopped. Expected work was incremental
compilation, not proof generation or elimination. No Lean ran; `#print
axioms` is **N/A** for every result here.

Two linker failures are retained in `build-default-failed-linker/` and
`build-default-failed-concatenated-flags/`: direct SBF `rust-lld` rejects
`-Wl,--threads=4`, and cargo-build-sbf concatenates the native and target
flags. Final SBF invocations remove native `RUSTFLAGS` only for that command
and use `CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4'`.
Native checks keep the requested `RUSTFLAGS='-C link-arg=-Wl,--threads=4'`.

An initial `build.rs` implementation compiled but reordered code and failed
the default pin (`7b631436…`, same size). It was replaced with const evaluation;
the discarded source is retained only on the host, and its receipts remain
under `build-default-build-script/` and `default-compare-build-script/`.
The `*-preformat/` receipts precede final formatting; final builds use the
committed source and reproduce the same final hashes. These were source or
linker-environment changes, not unchanged full regressions.

Final focused native program tests pass **34/34**, including the new decoder
and existing raw-buffer/checkpoint/authentication/route tests. The final byte
audit deliberately exits **1** on the rejected devnet build. Receipt source
hashes match revision `30eb0519a`. Final time/RSS/swap measurements are in
`build-default/time.txt`, `build-devnet/time.txt`, and
`final-native-checks/{test,audit-build,audit}.time`; each build also records
cgroup peak memory separately. No full unrelated regression was run.

| Final run at `30eb0519a` | Exit | Wall | Peak RSS KiB | Swaps | Cgroup peak bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| Default SBF build | 0 | 2.31 s | 202,748 | 0 | 137,592,832 |
| Devnet SBF candidate build | 0 | 2.33 s | 202,900 | 0 | 125,394,944 |
| Native program tests | 0 | 1.54 s | 245,844 | 0 | 160,768,000 (whole native-check scope) |
| Compile Rust byte auditor | 0 | 0.28 s | 135,792 | 0 | same scope |
| Byte identity gate | **1** | <0.01 s | 6,160 | 0 | same scope |

SBF logs retain the pre-existing dependency stack diagnostics; successful
compiler exits are not a claim of a new reachable-stack/CU release audit.

## Stage 1 — funding and retained identities

| Role | Retained public identity |
| --- | --- |
| Payer | Xjb7roDVPDSPoZpUmDVUW5SMx21x7oQEg16dhb5TDXD |
| Verifier | Gk16spfMwbZ1wK1B8Y8upLd7y2DDJQz73iZKU5GEVyBA |
| Pool | BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs |
| Registry | 9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q |

The eight-hour watcher started at **07:43:58 UTC**, verified the devnet
genesis, and observed 0 lamports at finalized slot **513088749**. Its first
hourly public `requestAirdrop` retry returned HTTP/RPC **429**, without a
signature. At the next five-minute poll, **07:48:58 UTC**, it observed
**5,000,000,000 lamports**, finalized context slot **513090011**, and exited
successfully. The funding threshold was reached after five minutes; no
further hourly retry or eight-hour timeout was needed. All requests,
responses, exits, UTC starts, curl timings, RSS and swaps are preserved in
`receipts/funding-watch-2/`. The watcher is inactive; it is not left running.

An incoming 5-SOL funding transfer (not signed or submitted by this worker)
landed at slot **513088870**, with `meta.err=null`, **450 CU**, fee **5,495
lamports**, and finalized status. Signature:
[3iX3Lg7…oodirhe](https://explorer.solana.com/tx/3iX3Lg7BRLCF323DYdq9UyHcFDzgzeFFHjR53E8tquhLWeWQkKQtufhFnrR8rdm6YnuZ6HY6vuGkvwY55oodirhe?cluster=devnet).
Its submission/confirmation wall time was not observed and is not inferred.
`receipts/funding-source/` contains the signature lookup and transaction meta;
`signatures.json` records it as external funding, never as an R1/deploy result.

Final account readback at finalized context slot **513091531** returns 5 SOL
for the payer and **null for all three reserved program accounts**.
`keys/` remains 0700 and all four JSON keys 0600. No funds were spent by this
worker; no refund, key deletion, unlink, burn or authority cleanup occurred.

Rent preflight is a second deployment constraint: RPC quotes **7.142871160
SOL** for candidate verifier programdata (1,405,904 + 45 bytes), **3.077855160
SOL** for Pool programdata (605,704 + 45), and **1.064021240 SOL** for registry
programdata (209,280 + 45): **11.284747560 SOL total**, before program accounts,
fees, setup or any temporary buffer requirements. Thus the requested 3-SOL
resume threshold is met, but the 5-SOL balance cannot fund all three programs.
No partial rent-consuming deployment was attempted while the required
release identity gate was false. RPC requests/timings: `receipts/rent-preflight/`.

## Stage 2 — registry, master, lanes, pages, mint and vault

**Not started.** No admitted devnet verifier exists under the data-only
release requirement. No registry was initialized or frozen, no mint or token
account was created, and no pool state was initialized. No deployment or
initialization signatures exist.

## Stage 3 — note deposit, retrying proof, uploads and spend

**Not started.** Deposits, P_R1 retrying proof generation, 3,763-byte TxV1
uploads plus statement, checkpoint creation, transfer, withdrawal, stage 1
and stage 2 all remain open. Their CU and wall times are **unmeasured**;
upload count is **0**. No nullifier/lane/vault state exists to read back.
A raw-buffer carrier and complete RPC driver are still required; the
admitted verifier continues to exclude legacy upload tags 4/5/6. The
compile-time constants change does not create an upload route.

## Stage 4 — negative checks

**Not run on devnet.** There is no consumed-checkpoint replay or mutated
proof stage-1 rejection signature. Native unit tests are explicitly not
reported as these requested RPC outcomes.

## Stage 5 — reproducibility and remaining work

Build, byte-audit and bounded funding-watch commands are in [README.md](README.md).
No partial utility is represented as an end-to-end spend driver. Needed next:
revise the impossible frozen-text/data-only release decision; admit and
validate the resulting artifact under that decision; provide sufficient
funding; then implement/run the carrier and full RPC setup/spend driver,
collect all phase meta/readbacks and both negative checks. Funding has
arrived, so this is not the eight-hour funding-timeout fallback. The decisive
stop is the false release-identity target, as required by the binding rules.
