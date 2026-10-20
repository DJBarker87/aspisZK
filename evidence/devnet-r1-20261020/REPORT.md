# R1 devnet continuation — 20 October 2026

In progress. The lead corrected the default verifier ELF pin; the former pin
obstruction is resolved. Frozen verifier source is unchanged. The prior
[pin-obstruction report](REPORT-pin-obstruction.md) is preserved as history.

Branch: `codex/cx-devnet3-20261020`. Frozen source/base: `fa894d83d`.
Driver source: `f17e756c19e802eb78791892b726a428528f8930`.
Host workspace: `/home/dombarker/project-offloads/codex-cx-devnet-20261020`.
All keys remain on the host, directory 0700 and files 0600. No key cleanup.
No binaries or keys are committed. `#print axioms`: N/A; no Lean run.

## (1) Release admission

The corrected preflight exits 0. Default ELF `dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34`
and devnet ELF `fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78`
are both 1,507,400 bytes. Section layouts and `.text` match; exactly the two
32-byte ID slots at 1,470,512 and 1,470,544 account for all differing bytes.
Pool: `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.
Registry: `7ad46f0d4b102a7c9699149d23bf6e065b6151feeaca95977d0a3146167d01ab`.
`f11e40b4…` remains the LLBC extraction hash, never an ELF.

## (2) Deployment

The first Solana CLI verifier deployment failed after 673.73 seconds:
`Data writes to account failed: Custom error: Max retries exceeded`.
Its retained buffer `3jhdwvMA6DMNwheHDewWvf2E2PUmiGP171dpQwLktd9z` holds
7,658,470,840 lamports. The buffer audit found 1,659 mismatching 900-byte
ranges. Payer readback: 8,788,444,160 lamports. The key remains retained.
A 3,763-byte loader write failed simulation with InvalidInstructionData;
no transaction was sent for that simulation. Paced 900-byte TxV1 repair
writes are in progress, with each batch confirmed finalized.

The external raw-buffer carrier is a new, separate transport-only program;
it requires the buffer account's signature for every bounded write. It has
no close, resize, authority-transfer or verifier operation. The optimized
SBF build passes: 20,136 bytes, SHA-256
`9d45bbcb0d68246993bd080f17f6ae116be48537e1a2c2bfd14602c590740ac2`.
Reserved carrier: `3jEFrv5Npn3RmFMW1Cbzq5yEiLdeFB5vbBGmnfoqK9vN`.

Registry V2 requires immutable loader deployments. The deployment driver
verifies ProgramData payload bytes against the pinned ELF before removing
the verifier/registry upgrade authorities, then verifies the unchanged
payload and absent authority. Keys are retained.

## (3) Initialization

Pending deployment. The config-driven driver uses actual SPL mint/token
instructions, Pool initialization, Registry V2 schedule/activate/freeze,
two vault-backed deposits and a permissionless forest checkpoint.
Fixture witnesses are intentionally public demonstration data; OS attempt
entropy and the durable nonce store feed the retrying P_R1 prover.

## (4) Transfer and withdrawal

Pending. Each proof is bound to finalized Pool lane/checkpoint bytes; the
historical paths are reconstructed from the two actual deposited leaves and
checked against the on-chain checkpoint root. Notes are selected so their
deposit and output lanes match, ensuring pages originate in real deposits.
The intended upload cadence is 16 proof uploads and one statement upload,
with maximum chunk length 3,763 bytes. No successful spend is claimed yet.

## (5) Negative checks

Pending. The driver sends tx2 again with a fresh blockhash and separately
mutates a compact proof byte before stage 1 with a fresh zero checkpoint.
It records both simulations and finalized failed-transaction metadata.

## (6) Driver and validation

`tools/r1-cost-probe/src/bin/devnet_spend.rs` signs TxV1 and plans the exact
ABIs; `scripts/r1_devnet_spend.py` orchestrates RPC execution from the public
config. Optimized compilation with `--features r1p-check` passes. The first
planner compile caught a missing witness import and a u64/u32 mismatch;
these were corrected. One subsequent build refused a stale lockfile; offline
resolution added only the P_R1 optional local dependencies, and compilation
then passed. The carrier build and Python syntax checks pass. All heavy jobs
run on the Linux host in separate 6G/8G/no-swap/64-task scopes.
