# NPC_ devnet result (Route B1): frozen Pool with a re-targeted verifier

The frozen Pool ELF e0e49c34 now runs on devnet at a new program id. It is paired with a verifier built from the frozen source with only the Pool id changed (ELF 2331ad8a). Both the honest transfer and the honest withdrawal settled on devnet through TX1 (verifier) and TX2 (Pool). Both replays were rejected with NullifierAlreadyConsumed, and both mutated stage-1 proofs were rejected with InvalidInstructionData; both proofs were restored. All 69 spend-phase transactions have full recordings, and the payer's lamports reconcile exactly. The verifier here is not the pinned release verifier 63ad3e9c; it differs from it in the 32-byte Pool-id slot alone. This is operational evidence on devnet (Agave 4.4.0), not a soundness theorem.

The lead gave the go on 2026-11-10, after the owner funded the payer with 10 devnet SOL, which the lead took as approval of B1 and of the verifier finalization the registry requires. The payer held 19.588839320 SOL before the first write.

## Why a new Pool id and a re-targeted verifier

The Pool program BmsNik... cannot be upgraded, because its authority key Xjb7roDV... is lost (NPC_PLAN.md). The pinned verifier 63ad3e9c accepts only BmsNik... as its Pool. The frozen Pool therefore went to a fresh id, and the verifier was rebuilt for that id.

## Step 1: funding gate (read-only)

devnet/NPC_funding_check.py is NDZ's gate extended to two new programs. It confirmed the retained keys (0600), the genesis, an empty buffer inventory, both new addresses absent, the pinned registry and carrier payloads, TxV1 active, and the legacy-SBPF deployment ban inactive. The conservative simultaneous peak of 20.295860040 SOL exceeded the balance by 0.707020720 SOL. Under the lead's rule, the gate passed on the basis of the expected spend (10.524553560 SOL) plus a 3 SOL margin, with 6.064285760 SOL to spare. The sequential conservative peak, which matches the deploy order actually used, was 18.539130000 SOL, with 1.049709320 SOL to spare. Receipt: devnet/NPC_devnet_receipts/NPC_FUNDING.json.

## Step 2: re-targeted verifier, new pin

The source was a git archive of 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 over NOX's input set; all 1,180 files are identical to NOX's B003 tree (vbuild/src_vs_nox.diff is empty). The recipe is NOX_B003: cargo-build-sbf 3.1.13, features pool-adapter,private-leaf-salts, under `env -i` with the NOX variables, no RUSTC_WRAPPER, and CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL not set. The only change is ASPIS_R1_POOL_PROGRAM_ID=37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt; the registry id is unchanged. The build used NOX's scope launcher (6G high, 8G max, swap 0, 64 tasks, 1800 s) behind the host reservation gate. Scripts: vbuild/NPC_vbuild.sh, vbuild/NPC_vscope.sh, each NOX's with the workspace path changed.

| Attempt | Ids | Result | Wall | Peak RSS | Cgroup peak | Swap |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| NPC_B001 | devnet (control) | exit 1: host lld thread spawn hit TasksMax 64 ("Resource temporarily unavailable") | 2.85 s | 265,140 KiB | 498,937,856 | 0 |
| NPC_B002 | retarget | 2331ad8a... (succeeded by timing; same shape) | 77.6 s | 647,688 KiB | 1,259,249,664 | 0 |
| NPC_B003 | devnet (control), CPU affinity 0-3 | 63ad3e9c..., byte-identical to the release pin | 106.3 s | 646,780 KiB | 1,240,334,336 | 0 |
| NPC_B004 | retarget, CPU affinity 0-3 | 2331ad8a..., byte-identical to B002 | 117.9 s | 648,732 KiB | 1,244,872,704 | 0 |

The B001 failure is the one NKX recorded, and the fix is NKX's: `taskset --cpu-list 0-3` outside `env -i`. That changes neither the build environment nor the caps. Cargo.lock stayed 5782e6a3... before and after. `#print axioms`: N/A.

New pin: **2331ad8a2d97439a30329328c51f619a6b13be97e260ab1e1fd8aab22cb996ea**, 1,563,728 bytes. Against 63ad3e9c it differs in 31 bytes, all within file offsets 0x174b70-0x174b8f, the 32-byte Pool-id slot in .rodata. The old slot holds BmsNik..., the new slot holds 37hdATMk... (one byte coincides), and the registry-id slot and every other byte are equal. The stop condition was not met.

## Steps 3 and 4: deployments

Both deployments used the writer container (the pinned image a5fd1959..., Agave CLI 4.2.0 b6134ccd..., client 77e7e541..., 4 GiB memory, swap 0, 256 pids; the payer mounted read-only). The script is NDZ's paced loader-v3 deploy, plus one addition: a ProgramData re-read immediately before finalization (devnet/NPC_deploy_paced.diff).

| | Frozen Pool | Re-targeted verifier |
| --- | --- | --- |
| Program | 37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt | GqZzWuGTojfsxYnDzmyWKhdPGkce19xN1Txu9Vgnr5hy |
| ProgramData | 8aCcqmxpGhq5un6hcxQBFRGYhpAC5oCpAUwDUneR2jyL | 9f4huzXEK5opApGDh1jvVVPPjnNdQJnCMUr3YcBbePsF |
| Payload | 345,648 bytes, e0e49c34..., exact | 1,563,728 bytes, 2331ad8a..., exact |
| Chunks | 385/385 | 1,738/1,738 |
| Deploy signature | 2niNc5GDpZVzp61MdFN2yhNp3ao243f8wHn6AAuAdWLCTcULvm8MMNide8LUy1UdXLcXoirMP29hYs6qqNSgX5VX | 5rWGKagFFaYh4rXe4AxR9Ws62rDhrm7cbLUWkCw6aQwH4TNNcpr5ndVYWXxrKLns9dJQUhJQsLKrboHzh5hKpjxx |
| Authority | payer CVZJcAv9... (not finalized) | none: finalized by HYqdH4joWKZWzkARUs17AkfnB7VQizFX6gvf9wZqcdVWQ1JU95TgCjLQeUVks57HeuTReCCyfTB3cRdpFaX155C at slot 520604638, after a pre-final re-check at slot 520604633 (payload 2331ad8a, authority payer) |
| Wall | 1,321.9 s | 5,936.6 s |

Both buffers were consumed by their deploys, and the buffer inventory under the payer is empty. Every loader transaction's finalized metadata is retained (devnet/NPC_devnet_receipts/NPC_deploy_pool/ and NPC_deploy_verifier_tx.tar.xz). All 387 + 1,741 succeeded.

## Step 5: registry, Pool state, spends

Through the same recording driver as B2 (local/NPC_spend.py), the run went:

- fresh mint 5eqB4AVUtUsCyb2tXSLJ1tu4G4P1ff5Nhg6nYHUjsSFG, source E6DHgpcDjgr7cd5RmXvoWAyfsHNRmALBvNcabNV27VBP, destination F1NL6ng1wcVevDB72u7CEpHbzXiKDSpUFJfGifv1zBVB;
- registry Hnn3D6DS6xmyodJkpXy8LgZc2tiGxVnoQK6k8Gyv98qq under 9pWwAc...: initialize EGUPZW8E..., schedule 4B6B6BKx... (verifier GqZzWuGT, hash 2331ad8a), activate 3951g3kv..., freeze gPoWHDoX...; entry 2DrbrBFVkCEcJDAxvzDGJTjvg7F3pXzxSXo1fMS5FodD;
- Pool master D7akkxLFyeTiShvx42KPdELPmmm711oEi1JuFdS3PXgK under 37hdATMk, and vault G6HQ64zFaHkQ2ZXJPHZoPWUEMRabAx9sf6oWVXkHYbjT.

| Step | Program/magic | CU | Result | Signature |
| --- | --- | ---: | --- | --- |
| pool-initialize | Pool AS8I | 124,374 | ok | 65nDh6VGuyG71NwSRcANcczGqbZiXXhuYUe9E4JggQKB5SCr4pK4rYSaK2FwMyzRc2ZV49JPxyFpiYk3hCaW2pK3 |
| deposit-0 | Pool AS8D | 1,106,971 | ok | 37ev7k57r8okb1BhsXBFH6yNonn3TsMbBkADRYkL95o2hSdVqAKmhsNcZxeCg4RrxHg6zqd1YQayjKS5thxxaomR |
| deposit-1 | Pool AS8D | 1,106,966 | ok | 2HDZhFXWxWzR9kVrfBPffCFd11EbztaoVHYhFWBXfvEp6v5hAHcEv8YG9Wg3xoSoxo6KA7vEbagFpuJz396QXmCZ |
| forest-checkpoint | Pool AS8C | 1,153,927 | ok | 3GLEzr5YXQX24KhTJwrNRbt1B22XfmJPzG7u7hheU2aKYwgECbUvrSfk9URjshAbvsxt3F3j2DHbGnLysWkQ6c4F |
| transfer-stage1 (TX1) | Verifier | 1,208,613 | ok, slot 520606640 | pUEwuhuSNmr8PK159eVxZhwJGHAceLr8qLLcE4b3gdJ3qTuFz9NgoGXwhe6VrL646VhRj6AzmSXuyuQTq8Hz4i8 |
| transfer-stage2 (TX2) | Pool ASQ8 | 1,138,552 | ok, slot 520606678; vault 2000, destination 0 | 5bPwiKGmcXgRQnEJfbUrxHU1kuQgu3Q4GMrZ8V76jCHTxmqr3zVKkjcsk5JNmP9PXtimkrQBzvf5SQ4Chq4UBmCt |
| transfer-replay | Pool ASQ8 | 67,240 | Custom 0x41532026; protected accounts unchanged | JjAbeFtzfWJ5JH6AyS6Gmz4Rh9dYyHjVtpyXfPzyCuDBwLSQ7Jb7ioPe9HC3AytHY8fgNTSwHyN3G2uVFJLqWzv |
| transfer-mutated-stage1 | Verifier | 21,453 | InvalidInstructionData; fresh checkpoint unchanged | 61R9NogGVvsjnjwwfiZUwwZ5wvYpLNBrEcrtXierLpiDDyzcji8kjydUQbU9NFYvUaHsdUA7fG3sMVQmSWCUzZL8 |
| transfer-restore-proof | Carrier | 430 | ok | 3BBFpKyxT5jFj41Gh1Fj188MMpXornNUnHvaFMxZG5zXrqUMKWngPb1uyms9Ptd663yLs5fZo8dLP84L9FUwouHn |
| withdrawal-stage1 (TX1) | Verifier | 1,211,252 | ok, slot 520607963 | 2QS4o2i1TpocPc4xeDh9KFBLuKaqBAbSTkiwiNbqecrNoTZvq1rjP8tVyu6BfBGuYFqJnpe4ueG3Ev5q7HvgjPpo |
| withdrawal-stage2 (TX2) | Pool ASQ8 | 1,153,431 | ok, slot 520608000; vault 1750, destination 250 | 54t54tQ14sNpUxU6cQJoi4e1Vpbb8bZhwMrDxmnrUk9fgEPBCmcZi3Qzwmc4F9SjmgoeTXfLDDZ7TfA8QBUjW8EM |
| withdrawal-replay | Pool ASQ8 | 68,841 | Custom 0x41532026; protected accounts unchanged | 5LMwbEXuJXPkRphdcoDqRLEEVHFrZ23iobGiTm3Wxy1PXrammxR5EGci5gN9923UXh75kS4CZYQ2NYJLVahH64xW |
| withdrawal-mutated-stage1 | Verifier | 21,395 | InvalidInstructionData; fresh checkpoint unchanged | 4T6bRQT81VHiN573eeNmrUZxVPzPFoQSJ6d3B97AZpB2Xrza7pF5qniqVfBBUXKGoEu7TVTLiwpWhz1PGbC97r4e |
| withdrawal-restore-proof | Carrier | 430 | ok | 3waTKdYefeDVXk2z2QfVer5oXzG5uAJLSQ26eR9PoHQwE2U49sWm2bpwT1tV7vzBGvpeWJyGhgDrsPsb2KYrcv3 |

The mutation flips the low bit of the proof header byte at offset 688, as in NDZ and B2. All 69 signatures with slot, CU, fee and error are in devnet/NPC_devnet_receipts/NPC_SUMMARY.json. The spend phase took 838 s wall.

Recording: devnet/NPC_devnet_receipts/NPC_TRANSACTIONS.json.xz (SHA256 ce85ee8c6b38fde3e6ec4625ce609646c15b043c4b24f04613b96cf754c66508; JSON SHA256 4328957521b92698d5e4cb33df222706b968599f7bdd2f941c4a97bfb15d2e23). It has the same content per transaction as B2: signed wire bytes, instruction metas and data, landed message flags, full pre/post images of every named account, an isolation check (true for all 69), the Clock slot and blockTime, and the finalized json/jsonParsed transaction with logs, inner instructions, return data and CU. The proof and statement bytes are the carrier images in each stage-1 pre-state. Syscall-level replies are not exposed by devnet RPC. ledger-tool `program run` inputs for every Pool, verifier and registry instruction are in NPC_REPLAY.tar.xz; NPC_LOCAL_RESULT.md gives the replay recipe and the 4.2.0 tool failure.

## Step 6: read-only association and accounting

One finalized read pass (NPC_ASSOCIATION.json, slots 520608504-520608524; byte checks in NPC_ASSOCIATION_BYTES.json):

- Verifier GqZzWuGT links to ProgramData 9f4huzXE, authority option 0 (immutable), payload 2331ad8a....
- Pool 37hdATMk links to ProgramData 8aCcqmxp, authority the payer, payload e0e49c34....
- The registry entry contains the verifier GqZzWuGT, its ProgramData 9f4huzXE and the hash 2331ad8a; it does not contain CSnhzGdH.
- The registry account Hnn3D6DS contains the master D7akkxLF.
- The master is owned by 37hdATMk, and its policy names the registry program 9pWwAc....
- The buffer inventory is empty (NPC_FINAL_BUFFERS.json).

The payer went from 19.588839320 SOL to 9.061065760 SOL, a difference of 10.527773560 SOL. That equals the 32 rent rows (10.494553560 SOL) plus the fees of all 2,197 transactions (0.033220000 SOL) exactly; see NPC_RENT_LEDGER.json. Of the rent, 8.734806000 SOL is permanently locked: the verifier's ProgramData and stub, the Pool stub, and the 0.788522680 SOL of fixtures with no close path. 1.759747560 SOL is recoverable. The Pool's ProgramData (1.756770680 SOL) can be recovered with `solana program close 37hdATMk... --recipient CVZJcAv9... --bypass-warning` under the retained payer authority, which is irreversible and needs the owner's OK. The source token account (0.002976880 SOL with the destination) can be recovered by SPL CloseAccount through the retained governance key, after the destination's 250 tokens are moved. These match the Phase 1 plan to the lamport.

All keys are retained at ~/.config/solana/aspis-deploy/NPC_frozen-20261109/ (directory 0700, files 0600). That covers the Pool and verifier program keys, both buffer keys, and the NPC_devnet fixture and proof keys. No key was copied, printed or committed. Nothing touched mainnet.

## Scope and limits

Operational evidence on devnet. The Pool is the frozen e0e49c34. The verifier is 2331ad8a, a new pin from the frozen verifier source that differs from the release pin 63ad3e9c in the Pool-id deployment constant alone. Whether the contract treats it as the frozen verifier is for the lead and owner; this run does not decide it. The pinned 63ad3e9c with e0e49c34 ran together only locally (NPC_LOCAL_RESULT.md). The devnet runtime is 4.4.0, while the writer CLI and client are 4.2.0 builds. RPC and finality are trusted as before. No premise was discharged, added or changed.

Target not yet established.
