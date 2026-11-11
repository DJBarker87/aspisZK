# Future-version experiment: one-transaction spend path on devnet (2026-11-11)

Experimental. This is not the release target. The R1 release target stays the PIN2 pin
(c7593d23fdc) with its two-transaction verifier; its 100-bit claim is "not yet established" and
nothing here changes that. The future verifier adds soundness obligations that are written down
in docs/research/future-version/SOUNDNESS-ROWS.md and are not proved.

## What is run

A fresh Pool state under the existing Pool program, two deposits, then a private transfer and a
withdrawal. For each payment the whole proof is verified and the payment settled in ONE
transaction. The proof is the pinned prover's proof re-packed into the summed format by a function
of public data (one multiproof per tree, then the 384-byte stage D certificate).

Per payment, 18 transactions:

| # | Transaction | Signed by |
|---|---|---|
| 1 | open: fund a fresh session key, create the proof account (56,503 bytes) and the checkpoint account (1,768 bytes), write the 58-byte tail | payer and session key |
| 2 to 16 | 15 writes of 3,763 bytes, signed against one blockhash and sent together | session key |
| 17 | verification and settlement | session key |
| 18 | close: proof account, checkpoint account, then everything the session key holds back to the payer | session key |

The payer stands for the user's wallet and signs one transaction per payment. The unchanged Pool
still passes a verifier-owned checkpoint account to the verifier; the one-transaction verifier does
not read it, so it is created zeroed and closed afterwards.

Test transactions, not part of a payment: before each settlement one byte of the certificate is
changed, the settlement is attempted and must fail, and the byte is restored; the same for one byte
of a Merkle node; after the settlement a replay must fail.

## Artifacts

| Item | Value |
|---|---|
| Verifier ELF (lean adapter A5: one-transaction entry, no stage 1 entry) | sha256 855687380d2c0255e02e8bc771a741e856fc47a7c99e2bfc713ea3675326c02c, 967,384 bytes |
| Verifier source | crates/ and programs/ at 8a4059c8bc2; build record out/A5-onetx-lean (cargo-build-sbf 3.1.13, platform-tools v1.52, devnet Pool and registry identifiers) |
| Pool ELF (deployed, unchanged) | e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc |
| Registry ELF (deployed, unchanged) | 7ad46f0d4b102a7c9699149d23bf6e065b6151feeaca95977d0a3146167d01ab |
| Upload program ELF (deployed, unchanged) | 9b2ab3d41695d81bfb79b93931d9323515fcc28a35fd725253be5e41bdc45874 |
| Client binary devnet_spend (features r1p-check, host Rust 1.94.1) | sha256 1db4b9c200514bebdaf1d7dd9dc4ef59d82ed2995a6db0eb0e4f7af8ba1b7094; planner source at c4b6a9e5ac1, unchanged since |
| Run scripts | this directory, at the commit that adds this file |

## Deployment (done 2026-11-11 13:23 UTC, owner go-ahead)

| Item | Value |
|---|---|
| Program | CmxQHrAx4qno6WRPMpWdRVp7MbyQiG7PhcfsVhuJaW92 |
| ProgramData | 61WQgQ6fHP4Ft39GFvG3MVsH33LCfWf1F6qVsJ9MJaba, upgrade authority none, deployed in slot 521116424 |
| Deploy signature | 5H33tiKSrzFLEVN52eaTFGfgbSWRmUkZkJD5zNoZRF2jm8HSET2khoVZiVHfYacVV2Wrfs64hzR2bDjap7kNwrsn |
| Locked rent | 4,915,189,560 lamports in ProgramData and 833,120 in the program account. Permanent: the registry accepts a verifier only with its upgrade authority revoked. |
| Payer before and after | 20.811659736 and 15.890544781 SOL (deployment fees 5,092,275 lamports) |
| Buffers left open | none (buffers-after-deploy.txt) |
| Preflight | receipts/FV_PREFLIGHT.json: deployed payload equals the ELF, verifier immutable, Pool, registry and upload program at their pins, TxV1 active, funding passes |

Keys: payer ~/.config/solana/aspis-deploy/devnet-payer-20261029.json; program and buffer keypairs
in ~/.config/solana/aspis-deploy/FV-20261111; run keys (mint, token accounts, governance, session
keys, seed records) in ~/.config/solana/aspis-deploy/FV_onetx-20261111. None is in the repository.

## Evidence before the devnet run

Replay (LiteSVM 0.16.0, Agave 4.2.1) of the recorded PIN2 devnet settlements against the A5 ELF,
replays-v3/: control reproduces the recorded compute units and final state; one transaction
completes at the 1,400,000 limit with the Pool instruction at 1,314,116 (transfer) and 1,320,621
(withdrawal) and final state equal to the control.

Rehearsals on a local validator (Agave 4.2.0, devnet feature set and the deployed Pool, registry
and upload programs cloned; verifier deployed and finalized by FV_deploy.sh; rent there is 6,960
lamports per byte, devnet's is 5,080):

| Rehearsal | Flow | Transfer settlement | Withdrawal settlement | Changed certificate | Changed node | Result |
|---|---|---:|---:|---:|---:|---|
| local2 (scripts at c4b6a9e5ac1) | payer signs everything, writes one at a time | 1,315,160 | 1,324,667 | fails after 1,295,715 and 1,302,136 | fails after 660,840 and 666,536 | complete: both payments settled, replays rejected, closes returned the rent, cleanup returned the token-account rent |
| local4 (scripts at f2d19288c62) | one approval, writes sent together | 1,310,614 | still running when this was committed | fails after 1,291,208 | fails after 659,264 | first payment complete: 18 transactions, the payer signed only the open, 15 writes confirmed 0.55 s after the first send (one slot, no network in the way), payer balance change equal to fees plus marker rent, session key emptied |

All figures are computeUnitsConsumed of the whole transaction. Both rejections are
InstructionError [0, InvalidInstructionData]. A second rehearsal attempt (local3) stopped in the
preflight, which read the finalized state before the authority revocation was final; the preflight
now waits for it.

## Predictions for the devnet run (registered before its first signature)

1. Both settlements succeed in one transaction. computeUnitsConsumed is in [1,309,000, 1,321,000]
   for the transfer and in [1,317,000, 1,331,000] for the withdrawal. A value under 1,400,000 but
   outside its band is a missed prediction and is reported as one.
2. Changed certificate byte: the settlement fails with InstructionError [0, InvalidInstructionData]
   after 1,285,000 to 1,312,000 compute units. Changed Merkle node byte: the same error after
   650,000 to 680,000. Replay: InstructionError [0, Custom 0x41532026]. No protected account
   changes in any of them.
3. Each payment is 18 transactions without the tests; the payer signs exactly one of them; the
   fee is 20,000 lamports for the open and 15,000 for every other.
4. The payer's balance falls by 2,086,880 lamports per payment in this run (1,706,880 nullifier
   marker rent, 380,000 fees including the seven test transactions; 1,981,880 for a payment
   without tests). The session key, the proof account and the checkpoint account do not exist
   afterwards.
5. The 15 writes are all confirmed within 15 seconds of the first send and none is re-sent. This
   one depends on the public RPC endpoint and is the least certain.
6. The cleanup returns 2,976,880 lamports from the two fixture token accounts.
7. The payer ends between 15.752 and 15.755 SOL.

## Rent that does not come back

| Item | Lamports | Why |
|---|---:|---|
| Verifier ProgramData and program account | 4,916,022,680 | immutable by the registry's rule |
| Pool state for the new mint (master, eight lanes, root pages, forest checkpoint) | 125,821,440 expected | the frozen Pool has no close for them |
| Registry state for the new master | 4,226,560 expected | the frozen registry has no close |
| Mint and vault token account | 2,555,240 expected | a mint cannot be closed; the vault belongs to the Pool |
| Two nullifier markers | 3,413,760 expected | the double-spend record; permanent by design |

Everything a payment creates besides its marker is closed by that payment.
