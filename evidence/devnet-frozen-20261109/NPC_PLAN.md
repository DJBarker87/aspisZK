# NPC_ plan: frozen verifier with frozen Pool on devnet (Phase 1, read-only)

Outcome: ROUTE B. The Pool program BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs cannot be upgraded by any key we hold. Its upgrade authority is Xjb7roDVPDSPoZpUmDVUW5SMx21x7oQEg16dhb5TDXD, the payer key recorded as lost on 29 October (docs/research/100bit-spend-path-20261013/design/DEPLOYMENT-SOL-RECOVERY-POLICY-20261029.md). The frozen verifier 63ad3e9c accepts only a Pool whose program id is BmsNik..., so the frozen verifier and the frozen Pool cannot run together on devnet without a different verifier ELF. Nothing was sent on chain. No key was created, and no secret byte was printed or copied.

## (a) Devnet state, read-only

Snapshot in NPC_DEVNET_READONLY.json (script NPC_readonly.py, getAccountInfo/getBalance/getSlot only), finalized slot 520502872, genesis EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG, solana-core 4.4.0.

| Account | State |
| --- | --- |
| Pool program BmsNik... | Upgradeable loader-v3, ProgramData D7VhQ5FwMPE7CEGprZDjbmiYbdRBqWEJ8Ezid791BwxY, 605,704-byte payload, 3.077855160 SOL, authority Xjb7roDV..., last deploy slot 513173584. Payload SHA256 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 (the pre-removal Pool). |
| Verifier CSnhzGdH... | Immutable (authority none), 1,563,728 bytes, SHA256 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299. |
| Registry program 9pWwAc... | Immutable, 209,280 bytes, ELF 7ad46f0d.... |
| Carrier 3jEFrv... | Upgradeable, authority Xjb7roDV... (also unrecoverable). ELF 9d45bbcb.... Used unchanged; no upgrade needed. |
| Fresh registry CRqLcv1M... | Owner 9pWwAc..., 256 bytes, magic ASR2, frozen (generation 3 per NDZ). |
| Active entry 6Hd8P6ne... | Owner 9pWwAc..., 320 bytes. |
| Fresh Pool master 4GQ9Gnmi... | Owner BmsNik..., 384 bytes, magic ASM8 (pair-forest master). |
| Vault 4kjEXoJ7... | SPL token account, 1750 base units (after NDZ's honest withdrawal). |
| Payer CVZJcAv9... | 9.588839320 SOL; no open buffers under it. Key present at ~/.config/solana/aspis-deploy/devnet-payer-20261029.json, mode 0600, public key checked. |
| Lost authority Xjb7roDV... | 3.708326000 SOL, system account, unmovable. |

Key search for Xjb7roDV..., by public key only (solana-keygen pubkey, nothing printed but the public key): 530 keypair-shaped JSON files on the build host under /home/dombarker and /tmp, no match. Mac home-directory scan: see the closing note in NPC_HANDOFF.md. This repeats the 29 October finding; it does not depend on it.

The verifier's dependence on the Pool id is verified by bytes as well as source. programs/r1-cost-probe/src/r1_pool_adapter.rs:79-81 places `ASPIS_R1_POOL_PROGRAM_ID` (build-time) in `.rodata.aspis_pool_program_id`. The adapter rejects any other Pool program at :535 (master/policy check) and :898 (terminal request check). The on-chain verifier payload contains the 32 bytes of BmsNik... exactly once, at file offset 0x174b70. The Pool has no `declare_id!` (programs/aspis-pool/src/processor.rs:3); its deployed payload does not contain its own id.

## (b) State compatibility of the frozen Pool with the fresh Pool state

The frozen Pool is state-compatible and workflow-compatible. The point is moot, because we cannot install it at BmsNik.... The basis:

- Pool source b936275 equals NKX's source revision 3c53b641 (empty diff over programs/aspis-pool, crates/, programs/r1-cost-probe, Cargo.lock, Cargo.toml). The deployed 121f3e29 is the frozen 4bb3b3f5 Pool (pinned in ADAPTER-RW-STAGE2-20261023.md:94 and ASQ8-KANI-20261021.md:221).
- 4bb3b3f5 to b936275 in programs/aspis-pool: 15 files, 13,336 deletions, 268 insertions. state.rs gains only a module comment and one `use`; vault.rs gains one `use`. The insertions are retained AS8I codec text and imports (NKX_REMOVED.md, NKX_BYTE_IDENTITY.json: 427 frozen body checks pass; pair*.rs byte-identical).
- The NDZ devnet run sent exactly these Pool magics: AS8I (pool-initialize), AS8D (deposits), AS8C (forest checkpoint), ASQ8 (stage 2 and replays). All four remain dispatched (b936275 processor.rs:508, 522, 536, 550), gated on pair-forest-account-evidence. That feature is on in the deployed feature set, through r1-split-checkpoint and pair-forest-source-invariant-audit; the resolved features are in NPC_pool1/pool1/receipt.json. None of the seven removed instructions (ASIN/ASDI/ASPT/ASWD/ASPP/ASPF/ASPX) was used.

## (c) Frozen Pool ELF rebuilt on the build host: byte-identical

| Field | Value |
| --- | --- |
| Target | cargo-build-sbf (Agave 3.1.13, pinned hashes asserted) for programs/aspis-pool, features r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit, --offline -j 4 --locked |
| Source | b936275465600469312d1f058cdc91ea2a11f3dc, git-archived to the same 1,235-path file set as NKX's tree. Per-file hashes are identical to NKX's src except three tools/r1-builder-reference/*.rs files. Those are not workspace members and not in the crates/programs manifest; git shows them unchanged 3c53b641..b936275, so NKX's host copy had local edits. Host copy verified identical to the local extract. |
| Driver | NPC_run.py = NKX_run.py with two changes (revision file name, 1800 s timeout); NPC_run.diff. NPC_launch.sh = NKX_launch.sh with the host directory changed. Same reservation gate, 40 GB disk gate, barrier. |
| Scope | systemd-run --user --scope, MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, TasksMax 64 (asserted inside the scope); reservation allowed=true; one other scope running on the host. |
| Env | CARGO_PROFILE_*, ASPIS_*, RUSTFLAGS removed; CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL not set. |
| Result | exit 0, wall 63.36 s, peak RSS 677,616 KiB, cgroup peak 1,791,164,416 bytes, swaps 0, Cargo.lock unchanged |
| Artifact | aspis_pool.so, 345,648 bytes, SHA256 e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc; cmp identical to NKX's pool1 artifact |
| #print axioms | N/A (no Lean target) |

Receipts: NPC_pool1/. The host workspace is /home/dombarker/project-offloads/codex-cx-devnet2-20261109. It holds no key files; the artifact directory carries only the non-key placeholder directory.

## (d) Route B: why ROUTE A is unavailable, and the options

ROUTE A needs the BmsNik... upgrade authority. That key is lost, so A is impossible. The frozen Pool can only go to a new program id P'. The immutable frozen verifier 63ad3e9c embeds BmsNik... and rejects any other Pool. So an honest TX1/TX2 pair with both the pinned verifier ELF 63ad3e9c and the pinned Pool ELF e0e49c34 cannot run on devnet. Any devnet pairing of the frozen Pool requires a verifier ELF other than the pinned one.

One supporting measurement bears on the options. NKX's default (f8c0ec72, placeholder ids) and devnet (63ad3e9c) verifier builds from the same frozen source differ in exactly 63 bytes. All of them lie in the 64-byte window 0x174b70-0x174baf, which holds the Pool-id and registry-id slots. A verifier built with ASPIS_R1_POOL_PROGRAM_ID=P' is therefore expected to differ from 63ad3e9c only in the 32 bytes at 0x174b70. That is a prediction from two builds, not a result for a P' build.

**Option B1: new devnet Pool program and a re-targeted verifier (needs an owner decision and funding).** Deploy e0e49c34 unchanged at a fresh P', upgradeable, with authority retained by the payer and not finalized. Build the verifier from the frozen source with only ASPIS_R1_POOL_PROGRAM_ID changed to P'. Byte-diff the result against 63ad3e9c and stop unless the difference is confined to 0x174b70-0x174b8f. Deploy it to a fresh verifier id V' and finalize it, because the registry accepts only an immutable verifier (programs/aspis-registry/src/processor.rs:208-217). Finalization needs the owner's explicit instruction. Then run NDZ's sequence: fresh registry under 9pWwAc, Pool state under P', both honest pairs, two replays, two mutated stage-1 proofs, two restores. The result would be a frozen Pool run with a verifier that is not the pinned release artifact. The contract would have to say whether an ELF that differs only in the Pool-id deployment constant counts as the frozen verifier; this worker does not decide that.

Rent and funding for B1 (devnet rate 5,080 lamports per byte including the 128-byte header):

| Item | SOL | Recovery |
| --- | ---: | --- |
| P' buffer (345,685 bytes, transient) | 1.756730040 | Consumed at deploy; on failure, `solana program close <buffer>` to payer |
| P' ProgramData (345,693 bytes) | 1.756770680 | Recoverable: `solana program close P' --recipient payer --bypass-warning` with the retained payer authority (irreversible; needs owner OK) |
| P' Program stub | 0.000833120 | Locked; loader-v3 has no stub close |
| V' buffer (1,563,765 bytes, transient) | 7.944576440 | As for P' buffer |
| V' ProgramData | 7.944617080 | Locked after finalization; before finalization, recoverable by program close |
| V' Program stub | 0.000833120 | Locked |
| Fixture accounts (NDZ devnet ledger, 28 accounts) | 0.791499560 | 0.002976880 SPL-closable by retained governance; 0.788522680 locked (no close path in the unchanged programs) |
| Fees (NDZ route 0.027415 plus about 385 extra Pool-buffer writes) | about 0.029 | n/a |
| Fee/retry reserve | 0.100000000 | n/a |
| Conservative peak (both double allocations live, NDZ method) | 20.295860040 | Payer 9.588839320: shortfall 10.707020720 |
| Expected spend at end | about 10.524 | Payer short by about 0.935 even on the expected route |
| Permanently locked | 8.734806000 | Verifier rent, two stubs, no-close fixtures |
| Recoverable afterwards | 1.759747560 | P' ProgramData plus SPL rent |

B1 cannot pass the funding gate on the current balance. It needs about 11 SOL more from the owner (faucet), sent to CVZJcAv9....

Keys B1 would need: the payer (above, read-only mount). New P' and V' program keys and two buffer keys, generated fresh and retained in ~/.config/solana/aspis-deploy/NPC_frozen-20261109/ (0700/0600, never in a workspace). The task key namespace NPC_devnet for mint, source and destination token accounts, governance, public/checkpoint and selected64 proof keys, under the same directory. No existing NDZ key is reused for a new role.

Transactions B1 would send, in order (each simulated first, then finalized, with a receipt):

1. P' deploy: create buffer, about 385 900-byte writes (paced, at most 60 before a finalized wait), full readback, DeployWithMaxDataLen (max-len 345,648), ProgramData byte check against e0e49c34. No finalization.
2. V' deploy: create buffer, 1,738 writes, readback, deploy, byte check against the V' pin, then `set-upgrade-authority --final` (owner instruction required), immutability check.
3. Fixture setup: mint create/initialize, source and destination create/initialize, mint supply 2000.
4. Registry: initialize, schedule (V' program/ProgramData/hash), activate after the finalized activation slot, freeze.
5. Pool under P': AS8I initialize, AS8D deposits 0 and 1, AS8C forest checkpoint.
6. Transfer: 16 proof uploads and 1 statement upload to the carrier, checkpoint create, stage 1 (V'), stage 2 (ASQ8 to P'). Then replay (expect 0x41532026), negative checkpoint, mutated stage 1 (expect InvalidInstructionData), proof restore.
7. Withdrawal: the same as 6. Expected vault 1750, destination 250.
8. Read-only association and an empty buffer inventory.

The NDZ total was 1,812 workflow transactions, mostly loader writes. B1 adds about 385 Pool-buffer writes.

Recording per transaction (B1, and any later route): signature; the full finalized getTransaction JSON (jsonParsed and base64) with meta.preBalances, postBalances, preTokenBalances, postTokenBalances, logMessages, innerInstructions, computeUnitsConsumed, fee and err. getAccountInfo base64 snapshots of every account in the message at the slot before submission and at the finalized landing slot. The Clock sysvar at the landing slot. The exact serialized transaction and each instruction's data bytes. For stage 1, the proof bytes as uploaded, the carrier readback hash, and the mutated variant's byte diff. These go to NPC_TRANSACTIONS.json, with large blobs gzip'd beside it.

**Option B2: local validator, both pinned ELFs, zero SOL (recommended first).** Run NDZ's local rehearsal unchanged in method on a pinned local validator. Clone the immutable devnet verifier 63ad3e9c, registry and carrier as NDZ did, and load the frozen Pool e0e49c34 at the address BmsNik... (the test validator's upgradeable-program/account override). Then run the honest pair and the four negative checks against the frozen verifier and the frozen Pool, with the complete per-transaction recording above. This is the only route that runs both pinned ELFs together. It is local, not devnet: it inherits NDZ's caveat that the local Agave 4.2.0 runtime is not shown equivalent to devnet 4.4.0. It spends nothing and writes nothing public. It needs one capped validator scope (NDZ used MemoryHigh 3G, MemoryMax 4G).

**Option B3: frozen Pool alone on devnet (low value).** Deploy e0e49c34 at P' (about 1.76 SOL recoverable, 0.0008 locked), initialize a Pool state, deposit and checkpoint, and show that the seven removed instructions reject. Stage 1 against 63ad3e9c would reject on the Pool-id check, so no honest spend pair is possible. This shows the frozen Pool executes on devnet, not the spend path.

**Option B4: stop.** Keep NDZ's 29 October devnet run (frozen verifier with the pre-removal Pool 121f3e29) as the devnet evidence, and state plainly that the frozen Pool has no devnet run.

Recommendation: B2 now, because it costs nothing and runs exactly the two pinned artifacts. Choose B1 only if the owner (a) accepts a verifier ELF that differs from the pin in the Pool-id constant, (b) instructs its finalization, and (c) funds about 11 SOL. Nothing is sent until the reply "go" names the option.

Target not yet established.
