# R1 devnet end-to-end result — 20 October 2026

**COMPLETE:** the pinned verifier, Pool and registry are deployed; initialization,
two spendable-note deposits, a transfer, a 250-base-unit withdrawal, both replay
checks and both mutated-proof stage-1 checks finalized on devnet. The external
raw-buffer carrier is deployed separately. **No frozen verifier source changed.**

Branch: `codex/cx-devnet3-20261020`; frozen source/base: `fa894d83d`.
The native driver used for both proofs is from `034c960c5`; the completed RPC
orchestration is `bda652809`. Their native Rust inputs are identical. The final
[proof source check](receipts/proof-execution-source-check.json) verifies 525
files, including the P_R1/C3 checker dependencies, with zero mismatches. Native
binary SHA-256: `04ba4c2b6b37238ffd3b44f1ec8b0b9946c3989017c41f276df6ba18cf1bbcfd`.
Early tooling receipts name their base revision while work was uncommitted;
they are historical attempts, not the final proof source identity.

Host: `dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-devnet-20261020`.
All 26 task key files and both note-recovery files remain retained and 0600;
`keys/` is 0700. No wallet/account key cleanup, refund or deletion occurred.
No binary, private key, proof binary or nonce ledger is committed. No Lean ran;
`#print axioms`: N/A. Earlier pin obstruction is preserved in
[REPORT-pin-obstruction.md](REPORT-pin-obstruction.md), superseded by the lead's
corrected ELF pins and the successful admission gate.

## (1) Release admission

The corrected gate exits 0: [identity](receipts/corrected-preflight/identity.json),
[summary](receipts/corrected-preflight/summary.json). The existing SBF build was
reused, not repeated.

| Artifact | SHA-256 | ELF bytes |
| --- | --- | ---: |
| Default verifier | `dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34` | 1,507,400 |
| Deployed devnet verifier | `fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78` | 1,507,400 |
| Pool | `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` | 605,704 |
| Registry | `7ad46f0d4b102a7c9699149d23bf6e065b6151feeaca95977d0a3146167d01ab` | 209,280 |
| Auxiliary raw-buffer carrier | `9d45bbcb0d68246993bd080f17f6ae116be48537e1a2c2bfd14602c590740ac2` | 20,136 |

Verifier section layouts and `.text` are identical. Exactly 63 differing bytes
are confined to the Pool/registry slots at file offsets 1,470,512 and 1,470,544;
substituting those two 32-byte slots reconstructs the complete devnet ELF.
`f11e40b4…` remains the Stage2.llbc extraction hash, never an ELF.
Genesis and TxV1 activation checks pass; RPC reports Solana 4.4.0-beta.0.

## (2) Deployment

All four deployments finalized; full signatures and explorer links are in
[signatures.json](signatures.json). Every deployed ProgramData payload was read
back byte-for-byte against its pinned artifact; the final inventory verifies
all four pins again.

| Role | Program | Deployment signature | Slot | ProgramData rent lamports |
| --- | --- | --- | ---: | ---: |
| Verifier | `Gk16spfMwbZ1wK1B8Y8upLd7y2DDJQz73iZKU5GEVyBA` | [5KpihAXhn6aZ…](https://explorer.solana.com/tx/5KpihAXhn6aZmBevkgtpyBVaupBJQtmDNErvHec5pGMVDY5jvqTuQSR8wC8tBPdQ6QwCzn6Crfy8vWLYzhCsqAyF?cluster=devnet) | 513,171,035 | 7,658,470,840 |
| Pool | `BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs` | [qbGNyBtpTqt8…](https://explorer.solana.com/tx/qbGNyBtpTqt8DrXE7sb5btn6HoUFbQVnQV4cx7a6mpeG3Bd6X4gfK1NjwEytF2WYR2nNe2UgWx8R9FNcYZyP1pr?cluster=devnet) | 513,173,584 | 3,077,855,160 |
| Registry | `9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q` | [59bMe8pLqmkf…](https://explorer.solana.com/tx/59bMe8pLqmkfz3vsdDAF3DN4cZdBpHCWUXF5mS89Kid79sVnKPL5F5J6EUQQuUyausYy2yjD6xv7L8L9sXK8F9RY?cluster=devnet) | 513,174,495 | 1,064,021,240 |
| Carrier | `3jEFrv5Npn3RmFMW1Cbzq5yEiLdeFB5vbBGmnfoqK9vN` | [5GT64oGXFkSS…](https://explorer.solana.com/tx/5GT64oGXFkSSNXUpfWc88C3JgV8pKSBY7n2WNZWv2LRM6q8SfAmfguk1vv8tqw9D3DdPmQ5QtNWAycdopjB9ER4w?cluster=devnet) | 513,174,657 | 103,169,720 |

Each 36-byte Program account holds another 833,120 lamports. Permanent rent is
11.802846600 SOL for the three requested programs, or 11.906849440 SOL including
the auxiliary carrier. Verifier/registry upgrade authorities were removed only
after payload readback, as Registry V2 requires; their final authorities are
None. Pool/carrier upgrade authority remains the retained payer.

The carrier is transport-only: it requires the raw buffer account's signature
and ownership for every bounded write. It has no close, resize or authority
transfer route. The frozen verifier's rejected lifecycle tags 4/5/6 were never
used for proof uploads.

Operational failures and recovery:

- Initial CLI deployment exhausted write retries after 673.89 s. Its retained
  verifier buffer held 7,658,470,840 lamports; no key was removed.
- A 3,763-byte loader write failed simulation with InvalidInstructionData and
  was not submitted. Loader repair uses 900 bytes; this is independent of the
  separate carrier's successful 3,763-byte proof uploads.
- Paced repair reached 1,380 finalized chunks, then a batch's blockhash expired
  after 1,140.52 s. Readback found 251 remaining mismatched ranges. The corrected
  driver fetches a fresh blockhash per write and repairs only mismatches.
- The successful remaining repair plus verifier/Pool/registry/carrier deployment
  run took 1,122.67 s. Temporary buffers were consumed by the loader; every
  corresponding key file remains retained.

All landed program/buffer signature histories are retained. The first CLI did
not expose unpublished/expired signing attempts in its empty stdout; those
signatures cannot be reconstructed. Loader-write CU is sampled, while all 75
core deployment/authority/setup/spend transactions have complete finalized CU
metadata with no missing entries.

## (3) Initialization and deposited notes

Mint `CHnSQGrPPiP2jPgiARzWF6jx169rsSHciXbszjpL3gV1` has 6 decimals and supply 2,000 base units. Source:
`6hy6xhsh7evJa9WhHk4nPdALY7H6yeqPh882smc1XhUH`; destination: `5mZHfocHAqKSFMA5J28SFGhX94EHqK9M58yUbPtDMR9Y`. Their token authority
is retained key `ALZGcQnvvfGuCLDYrNeiYszq3jgohHKQ3Tmyhk7jZq7S`; mint authority is the retained payer.
Seven SPL setup transactions finalized in the 40.10-s mint run.

Master: `8YRunNHbLqBUzeZYh7VK6jsJDUup4jA1qTcKvPy4i2Lf`; vault: `8KnSRSkCYtocwbeqcn9TR1JxEtE5TkVjNtXbaPofhqxx`. All eight lanes were
created through the real Pool initializer. Registry V2 initialization,
schedule, activate and freeze finalized with minimum activation delay **20
slots**, generation 3 and zero registry authority after freeze. Two actual
vault-backed deposits funded spendable 1,000-base-unit input notes; deposit
instructions created their root pages. The permissionless forest checkpoint
was then created from all eight real lane accounts.

| Phase | Slot | CU | Wall seconds |
| --- | ---: | ---: | ---: |
| pool-initialize | 513,174,681 | 130,605 | 2.964 |
| registry-initialize | 513,175,169 | 115,116 | 2.934 |
| registry-schedule | 513,175,182 | 771,988 | 2.964 |
| registry-activate | 513,175,282 | 11,988 | 2.874 |
| registry-freeze | 513,175,295 | 4,589 | 3.018 |
| deposit-0 | 513,175,704 | 1,102,503 | 4.998 |
| deposit-1 | 513,175,725 | 1,102,498 | 3.096 |
| forest-checkpoint | 513,175,738 | 1,153,953 | 2.864 |

Each historical witness is reconstructed from the deposited leaves and must
match the finalized checkpoint root. Each proof reads the current live output
lane. Notes were selected so deposit/output lanes match, avoiding fabricated
PDA account data. Witnesses are deliberately public fixtures; fresh OS attempt
secrets and a durable nonce ledger feed P_R1. Output note owner keys are derived
from retained note keys; 0600 `note-recovery.json` files remain host-only.

Two client errors were corrected before submission: zero activation delay
(`0x41533001`) and incorrect deposit token-account ordering (`InvalidMint`).
Their failed simulations and old plans remain in `receipts/spend/`. The valid
ABI is `[mint, source, source authority, vault, token program]`. No deployed
program was changed, and no failed initialization/deposit transaction landed.

## (4) Full transfer and withdrawal over RPC

Both proofs passed P_R1 on attempt **1**. Each compact proof is 57,607 bytes;
the raw proof buffer is **58,295 bytes** (688-byte candidate afterstate plus
proof). ASF8 statement: 1,880 bytes. Separate verifier checkpoint: 1,768 bytes.
Each spend used exactly **16 proof uploads + 1 statement upload**, 34 total,
with maximum payload 3,763 bytes and maximum serialized TxV1 size 4,058 bytes.
Full buffer byte readback passes before stage 1.

| Phase | Transfer CU | Transfer wall s | Withdrawal CU | Withdrawal wall s |
| --- | ---: | ---: | ---: | ---: |
| Retrying prove, P_R1 on | — | 37.128 | — | 37.026 |
| 16 proof + 1 statement uploads | 7,385 | ~257.738 | 7,385 | 58.716 |
| Stage 1 | 1,197,994 | 3.253 | 1,195,252 | 5.363 |
| Pool stage 2 / settlement | 1,135,083 | 5.348 | 1,146,410 | 5.335 |

Wall times include RPC simulation, submission and finalized confirmation;
proving includes witness compilation and the P_R1 check, not compilation of the
binary. Transfer uploads hit HTTP 429 while polling one signature. Fifteen
named uploads had complete receipts; the remaining signature was reconciled
from finalized history rather than resubmitted. Shared pacing now spaces all
RPC request starts by 0.65 s. Transfer upload wall includes the recovery gap
and starts at the first legacy simulation receipt mtime, so it is explicitly
receipt-based/approximate. Withdrawal upload timing starts at phase entry.
No clean-network throughput claim is made from the recovered transfer phase.

Settlement and readback:

- **Transfer**: [5cHVacEf8pQqcaaoFhTk2yfM8j8jkgQMRuQH4TnQtpKSmy229LxzowG2654cmvCeifzRrQJA7MAaDAyFBkyQJcZ3](https://explorer.solana.com/tx/5cHVacEf8pQqcaaoFhTk2yfM8j8jkgQMRuQH4TnQtpKSmy229LxzowG2654cmvCeifzRrQJA7MAaDAyFBkyQJcZ3?cluster=devnet), slot 513,177,064; lane next-pair index 2, root `5820d842ecd8ea4705f5482381124714ac7b06478c262b74ab7e710fbfaf9a16`; vault 2000, destination 0 base units.
- **Withdrawal**: [4NZ9hn4QYpDtRnSQTjqpptLYL1Hrm2biPUsmmrx6kKS3AofgiEemdJk2zuaAcYkWSLzkRw3LXgRfCHkMCXVQBPsS](https://explorer.solana.com/tx/4NZ9hn4QYpDtRnSQTjqpptLYL1Hrm2biPUsmmrx6kKS3AofgiEemdJk2zuaAcYkWSLzkRw3LXgRfCHkMCXVQBPsS?cluster=devnet), slot 513,177,753; lane next-pair index 2, root `2a23425ce5d3cc40311fe33ffa4a4946b5a5015d5fc0b8675c450d71adb2b758`; vault 1750, destination 250 base units.

Both nullifier markers decode to the expected identities. Both live lane
images match every field of the proved afterstate, including frontier. The
withdrawal executed the real SPL TransferChecked CPI: vault **1,750**, destination
**250** base units. Transfer leaves custody balances unchanged. Readbacks,
validation records, raw finalized tx metadata and all signatures are committed.
After negative mutation tests, both raw proof buffers again match their
original uploaded SHA-256 values.

## (5) Negative checks

All four negative transactions finalized with the expected errors:

| Check | Slot | CU | Wall s | Signature |
| --- | ---: | ---: | ---: | --- |
| transfer tx2 replay: NullifierAlreadyConsumed | 513,177,108 | 67,251 | 5.348 | [4Zsa4eP9t87v…](https://explorer.solana.com/tx/4Zsa4eP9t87vtdK1CjFid44gmnkJNjNFkQhizsRRbkjKcZ6nUmaoUwZfGFHxwrYehPEMCwgo5AWJAjWpV4J4qRCa?cluster=devnet) |
| transfer mutated proof header: InvalidInstructionData | 513,177,200 | 20,941 | 5.346 | [2Ax5QvQw94Xq…](https://explorer.solana.com/tx/2Ax5QvQw94XqxKuDGZz5HpAhsDvswTRUisE2isvrUeZHACfY3GwhjDjzCec87Hzi2bKB57RKXWAwVkmr6638HcAh?cluster=devnet) |
| withdrawal tx2 replay: NullifierAlreadyConsumed | 513,177,790 | 68,852 | 5.346 | [iscWwjX6tRc6…](https://explorer.solana.com/tx/iscWwjX6tRc6NvYiTXS3jtdd7eEDBSkLpB2DhRxjaUefC2Be2X4VqpTDPwdrDxSzVcyG5ngR8Mk3VPrcC5QzpZJ?cluster=devnet) |
| withdrawal mutated proof header: InvalidInstructionData | 513,177,876 | 20,883 | 5.361 | [n15fF7jZeRrt…](https://explorer.solana.com/tx/n15fF7jZeRrtHRXB74jF14YNbn6MLv1Bvh2FaUFFcSMZVnwLSGbCGpC8RVYFF2TjMrz9AqE3ax1NL1QVx4v4NHG?cluster=devnet) |

Replay must return the exact Pool `NullifierAlreadyConsumed` code
`0x41532026`, not merely any failure. Marker, lane, vault, destination and
positive checkpoint account values remain unchanged. The stage-1 test flips
the first byte of the compact proof header (buffer offset 688), leaving the
candidate and statement intact, and uses a fresh zero checkpoint. It returns
InvalidInstructionData and leaves that zero checkpoint unchanged. This is a
header-byte mutation check, not a claim of exhaustive cryptographic mutation
coverage. The byte is restored afterward; final inventory hashes confirm it.

## (6) Repeatable driver, resources and retained state

[README.md](README.md) gives exact host/scope/build/deploy/spend commands.
`tools/r1-cost-probe/src/bin/devnet_spend.rs` signs TxV1 and plans the native
ABIs/proofs; `scripts/r1_devnet_spend.py` orchestrates config-driven RPC execution.
The sender persists signed attempts, simulates before submitting, confirms
finalized metadata and only re-signs after expiry/no landed signature. It
reconciles interrupted submissions before a retry, as exercised by the live
429 recovery. Bounded shared RPC pacing and four concurrent disjoint upload
ranges are used. Fresh key namespaces and receipt directories support another
independent mint/Pool run without deleting or reusing earlier funded state.

The completed-run guard was exercised read-only: exit 0, no signing, no proof
generation and no transactions. No unchanged full freeze/Lean/runtime regression
was repeated. Metrics cover these two real devnet fixtures. No blocker remains.

Every large job used the dedicated Linux host and a separate systemd scope:
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; optimized Rust `-j 4`.
Native RUSTFLAGS was `-C link-arg=-Wl,--threads=4`; SBF passes `--threads=4`
directly to rust-lld. Per-run commands, exit, wall, peak RSS, swaps, cgroup peak,
source labels and no-Lean axioms status are retained in
[run-summary.json](receipts/run-summary.json) and each run directory. The first
transfer-proof/upload attempt peaked at 547,684 KiB RSS with zero swaps; the
successful reconciliation/withdrawal run exited 0 in 228.89 s, peak 538,912 KiB,
zero swaps. Both are far below the cap. Bulk auxiliary loader-CU collection was
intentionally stopped (exit 130/143) to reduce RPC contention; all final landed
histories and all 75 core transaction metadata records are complete.

Final [key/authority inventory](receipts/key-inventory.json): 26 retained key
files, 0600; `keys/` 0700; two 0600 output-note recovery files retained; payer
**3,708,326,000 lamports**. Pool/carrier upgrade authorities and SPL mint authority
remain the payer. Token-account authority remains the retained governance key.
Verifier/registry are immutable. Raw buffers/checkpoints and all their keys
remain retained even where rent cannot currently be refunded. No cleanup or
refund was attempted. The retained public refund destination is the payer
`Xjb7roDVPDSPoZpUmDVUW5SMx21x7oQEg16dhb5TDXD`; refund signature list is empty.

Public evidence contains 2,682 landed worker signatures (including auxiliary
loader traffic) plus the separately labeled historical external funding.
Loader histories supply their finalized slots; core spend/setup/deployment CU
comes from transaction meta. Old raw binary section snapshots are represented
by SHA-256/size sidecars; originals remain on the host. Private keys, recovery
files, proof binaries, nonce ledgers, ELF/LLBC and compiled caches are excluded.
