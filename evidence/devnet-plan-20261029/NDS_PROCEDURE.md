# NDS procedure — STOP: existing Pool cannot accept a new verifier

Inspection revision: e46139f960d83c5fb0f078cdc17add317c65a9a6. Read root AGENTS.md,
Security and proof discipline §6, and the 2026-10-29 deployment approval.
No release source, features, protocol, artifact pins, crates or programs changed.

## Wiring blocker

The historical Pool **state** is `8YRunNHbLqBUzeZYh7VK6jsJDUup4jA1qTcKvPy4i2Lf`;
Pool **program** is `BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs`.
Its registry PDA is `FUHo4ZRK5Q8TGkaMvUZhwyjXmCGz8qSR6hG19XwTycBr`,
owned by registry program `9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q`.
Finalized RPC slot 516372115 shows ASR2/version 3, flags=2 (immutable),
generation=3, and zero authority. Entry
`EN4AqiZ7N571XtMRvoa7dFyuRsz7y3Ef3oD3doB7nFtW` still stores historical
verifier `Gk16spfMwbZ1wK1B8Y8upLd7y2DDJQz73iZKU5GEVyBA`.
See NDS_RPC.json and NDS_STATE.json for original data/context.

The Pool does not compile in this verifier ID. In
`programs/aspis-pool/src/pair_forest_dispatch.rs:194–215`, the supplied verifier
is authenticated against the selected registry entry. In `src/registry.rs:283–390`,
Pool policy supplies the registry program and binding; the registry PDA is
bound to the Pool state, must be immutable, and the entry must match the selected
verifier/profile/release. Passing an unrelated fresh registry does not rewire it.

Registry `process_schedule_v2` (processor.rs:983) stores verifier program ID,
immutable loader ProgramData address and executable hash in a fresh entry.
It first calls `require_authority_v2` (:551), which rejects frozen registries
with RegistryFrozen. `process_freeze_v2` (:1189) sets immutable and zeros authority.
All V2 mutation routes require that authority; the exhaustive dispatch (:1263)
has no unfreeze or replacement-entry instruction. The spend script (:149–156)
initializes, schedules, activates, then freezes. Thus normal instructions cannot
add a verifier to this existing frozen Pool registry. Registry loader immutability
(reused NDQ association) also precludes patching the deployed registry code.

STOP under the explicit job gate. Existing-state wiring would need a changed
architecture/source/deployment scope. A fresh mint/Pool state with its own new
registry under the same existing programs is a possible source-preserving
alternative; the repository documents that repeat-demo route. It does **not**
rewire the existing Pool, migrate its notes, or establish custody continuity.
Return that scope choice to owner/lead before rehearsal.

## Keys and artifacts

Historical host: `dombarker@100.108.41.90`.
Documented key directory: `/home/dombarker/project-offloads/codex-cx-devnet-20261020/keys/`.
Files: payer.json → Xjb7roDVPDSPoZpUmDVUW5SMx21x7oQEg16dhb5TDXD;
verifier.json → Gk16spfMwbZ1wK1B8Y8upLd7y2DDJQz73iZKU5GEVyBA;
pool.json → BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs;
registry.json → 9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q;
carrier.json → 3jEFrv5Npn3RmFMW1Cbzq5yEiLdeFB5vbBGmnfoqK9vN.
These public identities are historical config values, **not fresh key checks**.
SSH stat found every documented file absent; permissions and current retention
location remain unresolved (NDS_KEYS_PUBLIC.txt). No key was created, copied,
read as bytes, modified or deleted. No new deployment identity was selected.

Release ELF (reused NCY evidence):
`/home/dombarker/project-offloads/codex-cx-native-elfpins-20261028/NCY_B001/artifacts/aspis_r1_cost_probe_program.so`,
1,563,728 bytes, SHA256
`63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`.
Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387, pool-adapter/private-leaf-salts,
compiled with the Pool/registry program IDs above. No rebuild or new artifact
verification ran. Historical config still pins fb2fc048…; it is unsafe to run
unchanged for this release.

## Deployment mechanism and funding

r1_devnet_deploy.py deploys through loader-v3 using retained program/buffer keys;
it does not finalize authority itself. r1_devnet_deploy_paced.py writes 900-byte
chunks, verifies buffer bytes, deploys with --max-len equal to ELF length,
checks ProgramData payload, then runs `solana program set-upgrade-authority
PROGRAM --final` for verifier/registry and checks metadata byte 12 is zero.
Finalization must follow byte verification. r1_devnet_after_deploy.sh automatically
runs the public spend script; do not execute it here. Build script exports the
two deployment IDs; no rebuild is needed for this unchanged release ELF.

Live payer balance: **3.708326 SOL**, finalized slot 516372100.
Live rent queries (lamports): buffer size 1,563,765 → 7,944,576,440;
ProgramData size 1,563,773 → 7,944,617,080; Program size 36 → 833,120.
Permanent account rent: **7.945450200 SOL**. The paced route first funds a
**7.944576440 SOL** buffer; transient conservative reserve for both allocations
is **15.890026640 SOL**, excluding fees, before loader buffer refund/reuse.
The payer cannot even fund the buffer (short **4.236250440 SOL** before fees).

At 900 bytes/write: ceil(1,563,728/900)=1,738 writes. Assuming 5,000 lamports per
signature and no priority fee, write fees ≈0.008690 SOL, plus buffer-create,
deploy and finalization signatures (budget ~0.00005 SOL). Permanent deployment
budget ≈**7.9542 SOL**; conservative transient budget ≈**15.8988 SOL**.
Fee rate/signature count are estimates, not an allowed live fee quote or rehearsal
measurement. Allow additional retry fees and wiring/spend rents once scope is set.
No funding, airdrop, transaction or signature was sent.
