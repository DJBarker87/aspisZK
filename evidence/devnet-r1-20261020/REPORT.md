# R1 public devnet attempt — 20 October 2026

Status: **BLOCKED; demo go/no-go is NO-GO on this evidence**. No program was
deployed and no R1 transaction was submitted. This is not LiteSVM evidence.

Branch: `codex/cx-devnet-runner-20261020`; inspected source/base:
`e90cf2f800f7177e5cca47aa7e5ba59a940130dd`. Host:
`dombarker@100.108.41.90`; retained task directory:
`/home/dombarker/project-offloads/codex-cx-devnet-20261020`.

## Stage 1 — fresh identities, funding and deploy preflight

Generated fresh devnet-only keypairs on the host. Directory `keys/` is 0700;
each key file is 0600. All keys remain there, including unfunded program keys.
No secret key material, ELF, mainnet identity or real funds were used or committed.
`receipts/identities.txt` records the public identities and modes.

| Role | Public key (reserved; programs NOT deployed) |
| --- | --- |
| Payer | Xjb7roDVPDSPoZpUmDVUW5SMx21x7oQEg16dhb5TDXD |
| Verifier | Gk16spfMwbZ1wK1B8Y8upLd7y2DDJQz73iZKU5GEVyBA |
| Pool | BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs |
| Registry | 9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q |

Confirmed devnet genesis `EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG`.
Host Solana CLI is 2.3.0. Funding attempts:

1. `solana --url https://api.devnet.solana.com airdrop 5 --keypair keys/payer.json`:
   exit 1, "Error: airdrop request failed. This can happen when the rate limit
   is reached." Subsequent CLI balance: **0 SOL**. Original CLI wall time/RSS
   were not instrumented; no timing is inferred.
2. Raw `requestAirdrop` for 1,000,000,000 lamports to the same payer, finalized
   commitment: curl exit **22**, HTTP/RPC **429**. Exact response in
   `receipts/airdrop-1.json`: "You've either reached your airdrop limit today
   or the airdrop faucet has run dry. Please visit https://faucet.solana.com
   for alternate sources of test SOL". Wall/RSS/swap: `airdrop-1.time`.

Neither returned a signature. There are no landing slots, CU measurements,
uploads, or phase timings. Counts: deploys 0; R1 submissions 0; uploads 0.
`signatures.json` deliberately contains an empty transaction list.

### Pinned artifacts verified, not deployed

Read-only SHA-256 checks on the retained host artifacts match the adoption pins:

| Program | Bytes | SHA-256 |
| --- | ---: | --- |
| Verifier | 1,405,680 | 8cf8d84ed0fe340a190b4f40a9f953f0e0523370299ba3ec8bbed9d65b88ace3 |
| Pool | 605,704 | 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 |
| Registry | 209,280 | 7ad46f0d4b102a7c9699149d23bf6e065b6151feeaca95977d0a3146167d01ab |

Paths and hashes: `receipts/artifacts-source.sha256`. Authoritative build
features/toolchains: `docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/artifacts-sha256.txt`.
Existing artifacts were inspected; no Rust/SBF build or Lean run was launched.

### Independent source obstruction — fresh program IDs cannot settle

The pinned verifier's `programs/r1-cost-probe/src/r1_pool_adapter.rs`:

- Lines 77–79 hardcode Pool `[0x41;32]`, registry `[0x44;32]`, policy `[7;32]`.
  The program addresses are `5PjDJaGfSPJj4tFzMRCiuuAasKg5n8dJKXKenhuwZexx`
  and `5bV6jUfhDHCQVA1WfKBUnXUsboJgoKgkzkKcxr3joew5`.
- `validate_asq8` rejects `request.pool_program != AUDIT_POOL_PROGRAM`
  with `InvalidInstructionData` before account authentication (line 880).
- `authenticate_invariant_release_registry` (lines 517–523) requires those
  Pool/registry identities, zero registry authority and the audit policy.

Consequently the requested fresh Pool/registry deployments cannot satisfy this
ELF's settlement path. This is a source-level obstruction, not an observed
devnet rejection. These three source files (`lib.rs`, `r1_pool_adapter.rs`,
`pool_route.rs`) match the retained adoption build tree byte for byte, as
recorded in the SHA receipt. No assumption that fresh keys control the audit
program IDs is made. Changing these constants changes the verifier ELF and
requires a new approved release pin and relevant Rust gates.

Further, `lib.rs`'s release entrypoint guard calls `pool_route::admitted`, which
admits only `[3,10]`, `[3,11]` and `ASQ8…`. Legacy upload opcodes 4/5/6 are
unreachable. The harness's 3,767-byte lifecycle uploads therefore cannot simply
be submitted to this pinned verifier. A supported writable buffer carrier is
needed; stage 1 accepts raw buffers of any owner. No carrier was deployed here.

V7 patterns were read using `git show origin/main:<path>` (public config,
results summary/commands, registry child and lifecycle/simulation scripts).
The historical V7 summary itself records an identity/artifact blocker; its
finalized setup signatures are not evidence of any R1 deployment.

## Remaining stages — not started

Stage 1 is incomplete: fund the retained devnet payer, resolve the incompatible
identity requirements, then deploy and read back matching program bytes with
finalized signatures/slots. Do not spend rent deploying the incompatible set.

Stages 2–4 remain entirely open: create mint and token accounts; initialize
registry/master/lanes/pages/vault; deposit a spendable note; generate witnesses;
prove with `prove_masked_retrying` and feature `r1p-check`; use a supported
carrier for proof/statement uploads; create verifier checkpoint; transfer and
withdraw via RPC; record finalized CU/wall measurements and account readbacks;
test consumed-checkpoint replay and proof mutation rejection.

Stage 5 (the complete spend driver) also remains open. No stub is presented as
an end-to-end driver. The config and read-only preflight documented separately
are resumption aids only. Funding alone will not resolve the identity mismatch.
No refund or key cleanup was attempted; retain every task key.

## Independent resumption tooling — read-only preflight

Added `scripts/r1_devnet_preflight.sh` and public config
`config/r1-devnet.template.json`; exact commands are in `README.md`.
These are not the requested stage-3 spend driver and do not advance stage 2.
Shell syntax validation passed. Host execution completed its observations and
returned the documented non-readiness exit 4: **0.62 s**, peak **13,728 KiB**,
**0 swaps** (`receipts/preflight.time`). All five RPC requests succeeded.
Source revision for program inspection remains the base above; tooling SHA-256
is recorded in `receipts/preflight-tooling.sha256`.

Finalized account readback at context slot **513087061** returned null for all
six accounts: payer, fresh verifier, fresh Pool, fresh registry, audit Pool,
audit registry. Thus the payer has zero lamports, none of the reserved program
IDs is deployed, and the hardcoded audit programs are also absent at that slot.
No source-controlled address can be relabeled as a successful deployment.

The TxV1 feature account is present, Feature-program-owned, non-executable,
with nine-byte data `AQCmWh0AAAAA` (active tag 1); the RPC reports
`solana-core: 4.4.0-beta.0`, feature set `1855282951`.
`receipts/preflight/` preserves requests, raw responses, HTTP codes, curl wall
times and exits. Summary: local ELF pins match **true**, configured IDs match
pinned verifier **false**, spend ready **false**. Prove/upload/tx1/tx2 timings
and CU remain **unmeasured**, not zero-valued successful phases.
