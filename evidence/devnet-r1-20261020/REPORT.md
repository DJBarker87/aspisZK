# R1 devnet resumption — cx-devnet3, 20 October 2026

**BLOCKED by contradictory release identity instructions.** The frozen-source
build and data-slot identity check pass. No transaction was signed or submitted.
The requested end-to-end RPC result remains incomplete.

Branch `codex/cx-devnet3-20261020`; source/base
`fa894d83d2f3ad6df34bc8493881c780621d553e`; frozen verifier source
`b2727acd3abf79315d18b754a260f58f4b1c6326`. No verifier source changed.
Host: `dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-devnet-20261020`.
The [prior report](REPORT-prior-cx-devnet2.md) preserves earlier failures and
funding observations. Its instruction-immediate obstruction is superseded by
the current freeze and does not apply to this build.

## Release pin obstruction

The task and `docs/research/100bit-spend-path-20261013/design/LEAD-FREEZE-20261020.md`
call `f11e40b4119578eee1ebef90874f436dc35b1076f6db27baaa92a79c0919538d`
the default verifier ELF hash. The referenced
`evidence/freeze-20261020/{FREEZE.md,artifacts-sha256.txt}` assigns that hash to
**Stage2.llbc**, 7,009,202 bytes. Host readback confirms the SHA and JSON
prefix `7b226368`, rather than ELF magic `7f454c46`.

The inventory's default verifier ELF is
`dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34`.
The gate records both facts rather than silently replacing the requested pin.
Common rule 4 in the supplied `r1p-common.txt` says: "If a target statement is
ill-typed or false, STOP that item, write the obstruction/counterexample in your
report, and continue independent items."
Clarification to use the documented ELF pin was requested; no answer had
arrived when these receipts were collected. Correcting this hash reference
requires no verifier source change.

## Stage 1 — build and identity

Tracked `crates/`, `programs/` and root Cargo inputs were synchronized from
this worktree into the existing task workspace; its compiled cache was reused.
All verifier files and Cargo inputs in the freeze manifest match exactly.
`receipts/resume-source-check.json` discloses one environment difference:
the host lacks `.cargo/config.toml`, which defines only the unused `xtask`
command alias and supplies no build flags. The rebuilt ELF nevertheless
reproduces the freeze exactly. No shared workspace/cache was overwritten.

| Artifact | SHA-256 | Bytes |
| --- | --- | ---: |
| Retained default verifier | `dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34` | 1,507,400 |
| Rebuilt devnet verifier | `fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78` | 1,507,400 |
| Retained Pool | `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` | 605,704 |
| Retained registry | `7ad46f0d4b102a7c9699149d23bf6e065b6151feeaca95977d0a3146167d01ab` | 209,280 |

Section layouts and `.text` are identical. Replacing only the Pool slot at
file offset **1,470,512** and registry slot at **1,470,544** reconstructs the
entire devnet ELF. Exactly **63 bytes** differ, all within those slots.
`receipts/resume-preflight/identity.json` records layouts, slots, hashes and
magic bytes. No ELF, LLBC, keys or target directories are committed.

| Run | Exit | Wall | Peak RSS KiB | Swaps | Cgroup peak bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| Optimized devnet SBF build | 0 | 30.30 s | 648,620 | 0 | 1,034,383,360 |
| Read-only release/RPC gate | 4 | 1.16 s | 34,784 | 0 | 33,669,120 |

Receipts: `build-frozen-devnet/`, `resume-preflight-run/` and individual
requests/responses/timings under `resume-preflight/`. Exit 4 records the
requested default ELF-pin mismatch; all other checks pass. Both runs used
separate scopes: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64.
No other worker scope was observed; `resume-reservations.txt` records the
preflight reservation. Before the build, inspection also showed only
`init.scope`; the new build reserved 8 GiB, below the 55-GiB host ceiling.
SBF used `--offline --locked -j 4`, with direct-lld `--threads=4`; the wrapper
records the requested native RUSTFLAGS. Expected time was incremental
compilation then byte comparison/RPC, not proving or elimination.
No Lean ran; `#print axioms`: N/A. Compiler stack diagnostics are preserved;
this build is not a new stack or universal CU audit. No full freeze regression
was repeated.

## Stage 2 — deployment, funding and keys

Finalized account context slot **513151589**: payer **16,447,000,000 lamports**;
all three reserved program accounts **null**. Genesis matches devnet.
RPC reports Solana `4.4.0-beta.0`, feature-set `1855282951`. TxV1 is
finalized-active at slot **492480000**. No RPC error/rate limit occurred.

| Role | Reserved identity | Programdata rent lamports |
| --- | --- | ---: |
| Payer | `Xjb7roDVPDSPoZpUmDVUW5SMx21x7oQEg16dhb5TDXD` | — |
| Verifier | `Gk16spfMwbZ1wK1B8Y8upLd7y2DDJQz73iZKU5GEVyBA` | 7,658,470,840 |
| Pool | `BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs` | 3,077,855,160 |
| Registry | `9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q` | 1,064,021,240 |

Programdata sizes include the 45-byte loader header. Each 36-byte program
account adds 833,120 lamports. Permanent program rent totals **11.802846600
SOL**, leaving **4.644153400 SOL** before fees/setup. Quotes exclude temporary
loader buffers; this is not a completed deployment funding simulation.
Funding is not the present stop.

Deployment signatures/slots and actual programdata rent: **unmeasured; no
deployment performed**. `keys/` remains 0700; all four existing JSON keys
remain 0600. No key deletion, unlink, burn, regeneration, repository copy,
refund or authority change occurred.

## Stages 3–5 — initialization, spends and negative checks

| Phase | Status | CU | Wall | Submitted signatures |
| --- | --- | --- | --- | ---: |
| Registry release, master, lanes, pages, mint, vault | Not started | Unmeasured | Unmeasured | 0 |
| Spendable note deposit | Not started | Unmeasured | Unmeasured | 0 |
| Transfer / withdrawal P_R1 retrying prove | Not run | N/A | Unmeasured | 0 |
| Proof and statement uploads | Not run; **0 uploads** | Unmeasured | Unmeasured | 0 |
| Transfer / withdrawal tx1 | Not run | Unmeasured | Unmeasured | 0 |
| Transfer / withdrawal tx2 / settlement | Not run | Unmeasured | Unmeasured | 0 |
| Consumed tx2 replay / mutated proof tx1 | Not run | Unmeasured | Unmeasured | 0 |

No marker, lane or vault was initialized/read back as a settlement result.
No claim of 16+1 uploads, settlement or negative rejection is made. Historical
external funding remains separately identified in `signatures.json` and is
not counted as this worker's transaction.

## Stage 6 — repeatability and remaining work

[README.md](README.md) documents the build and config-driven **read-only release
gate**. This is not the requested complete RPC spend driver. Its exit 4
preserves the unresolved requested pin. The historical template's artifact
paths and rejected candidate have been updated to the reproduced frozen build;
old configurations remain in prior receipts.

After resolving the pin: deploy the devnet ELF and pinned Pool/registry;
implement the external raw proof/public buffer carrier (the frozen entrypoint
rejects lifecycle tags 4/5/6 and admits foreign-owned raw buffers); initialize
accounts through actual instructions, create the SPL mint and deposit;
generate live-state transfer/withdrawal witnesses with P_R1 on; upload
3,763-byte chunks (16 proof + 1 statement); create checkpoints; send tx1 then
Pool tx2 with expiry/retry handling; collect finalized signatures, slots, meta
CU, phase times and marker/lane/vault readbacks; run both negative checks;
finish the reusable RPC spend driver. None of these open items authorizes a
frozen verifier source edit.
