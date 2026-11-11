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

## Results of the registered run (devnet, 2026-11-11, 13:30 to 13:46 UTC)

Receipts: receipts/FV_spend (71 transactions with the cleanup). The run stopped once, six
transactions in, on the public endpoint's transient history error (-32019) after
destination-initialize had landed; it was resumed with a bounded retry for that error
(b70dcc3fe4a). That one transaction has no before/after recording; its finalized metadata is kept.

| Prediction | Result |
|---|---|
| 1. Transfer settles in one transaction, 1,309,000 to 1,321,000 | Settled at 1,308,068. MISSED by 932 below the band. Margin to the limit 91,932. |
| 1. Withdrawal settles in one transaction, 1,317,000 to 1,331,000 | Settled at 1,321,318. Met. Margin 78,682. |
| 2. Changed certificate byte rejected, 1,285,000 to 1,312,000 | InvalidInstructionData after 1,288,670 and 1,298,768. Met. |
| 2. Changed node byte rejected, 650,000 to 680,000 | InvalidInstructionData after 658,327 and 665,434. Met. |
| 2. Replay rejected, protected accounts unchanged | Custom 0x41532026 both times, accounts unchanged. Met. |
| 3. 18 transactions per payment, payer signs one, fees 20,000 and 15,000 | Met for both payments. |
| 4. Payer balance change 2,086,880 per payment (1,981,880 without tests) | 2,086,880 and 1,981,880 for both. Session key, proof account and checkpoint gone. Met. |
| 5. 15 writes confirmed within 15 s, none re-sent | 10.57 s and 10.65 s, none re-sent. Met, but the figure measures this script: the shared transport spaces calls 0.65 s apart, so the sends took 9.2 s to leave and landed in 15 different slots. |
| 6. Cleanup returns 2,976,880 lamports | 2,976,880. Met. |
| 7. Payer ends between 15.752 and 15.755 SOL | 15.753457781 SOL. Met. The run cost 137,087,000 lamports outside the deployment. |

Settlement transactions:
transfer 2S8hoUe1QYg8YsD8eYzEzdkpSNTHpjVQysVDvNi8VJRmQcNuNtpJYpb5dtrycNaRiinrikCg3GQzk2MwKi6EV9Fg,
withdrawal 3bHPFX7FVCWFmi374UEtDTsr9jqNQ9tzzbmq948qG1KwVweL9hi6vvGSprCMeekaaviXsMySsuqTv69eMboAPhYb.

The missed band: the transfer has now been measured at 1,308,068 (devnet), 1,310,614, 1,315,160 and
1,316,145 (local validator) and 1,314,172 (replay of the PIN2 proof). The spread between proofs is
about 8,100 compute units; the band was 12,000 wide but centred too high.

What this run is: a fixture measurement on one fresh Pool state with two proofs. It is not a
bound over all inputs. Root-page rollover and a Pool with a long history were not exercised.

## Timing run: what it is and its predictions (registered before its first signature)

The same deployed verifier, a second fresh mint and Pool state (key namespace FV_timing), two
payments in "mode": "timing": all 18 transactions of a payment are signed first, then sent in four
phases (open; the 15 writes at once; settlement; close), each awaited to confirmation only, each
transaction broadcast to two endpoints (a private RPC endpoint and the public one). No negative
tests. The clock starts at the first send. Proving time is not part of it. The same validation and
accounting then run on the finalized transactions.

Rehearsal on the local validator (local5): first send to settlement confirmed 1.06 s for both
payments; open, writes and settlement in three consecutive slots; accounting exact.

1. Both payments settle. Settlement compute units: transfer 1,303,000 to 1,321,000, withdrawal
   1,315,000 to 1,331,000.
2. First send to settlement confirmed: under 8 seconds for each payment, and at most 15 slots from
   the open to the settlement.
3. The 15 writes are confirmed within 3 seconds of the start of their phase; none is re-sent.
4. 18 transactions per payment, the payer signs one; the payer's balance falls by 1,981,880
   lamports per payment; session key, proof account and checkpoint gone.

## Results of the timing run (devnet, 2026-11-11, 13:47 to 13:56 UTC)

Receipts: receipts/FV_timing; config FV_devnet_timing.json (the private endpoint's address is not
recorded). Both payments completed; the same validation and accounting as the registered run then
passed on the finalized transactions.

| | Transfer | Withdrawal |
|---|---:|---:|
| Open confirmed | 1.49 s | 1.47 s |
| 15 writes confirmed (all in one slot) | 3.06 s | 3.13 s |
| Settlement confirmed | 4.53 s | 4.52 s |
| Close confirmed (rent returned) | 5.96 s | 5.95 s |
| Slots from the open to the settlement | 13 | 13 |
| Settlement compute units | 1,312,109 | 1,321,189 |

Times are wall seconds from the first send with all 18 transactions signed beforehand, to
confirmation (not finality), from this Mac through a container, each transaction broadcast to two
endpoints. They do not include proving.

| Prediction | Result |
|---|---|
| 1. Settlement compute units: transfer 1,303,000 to 1,321,000, withdrawal 1,315,000 to 1,331,000 | 1,312,109 and 1,321,189. Met. |
| 2. First send to settlement confirmed under 8 s; at most 15 slots | 4.53 s and 4.52 s; 13 slots. Met. |
| 3. Writes confirmed within 3 s of the start of their phase; none re-sent | 1.57 s and 1.66 s; none re-sent. Met. |
| 4. 18 transactions, payer signs one, payer balance falls by 1,981,880 per payment | Met for both. Cleanup returned 2,976,880 lamports. |

Settlement transactions:
transfer 2SCDN6j4YX8ic6Zm3N9tjj6GLJpDqLw62t2L6xHr1stMfUEhiXEviLvix5L6DjigFikZLgo2ecBGxJzNax8KvjEf,
withdrawal 3RY1xTw5AwMSDx6MFSYCmN7NKiA56tDrBoXXvDTTFsrrGmbjzHLPA4Kn9kprjQbpWFQgzVmyuQtKswW6diCLM27Q.

The payer ended at 15.616580781 SOL; this run cost 136,877,000 lamports, of which 132,603,240 is
the second fresh Pool state, registry entry, mint and vault (no close path in the frozen programs)
and 3,413,760 the two nullifier markers.

## Proving time (separate measurement, not part of either run)

One proof on this Mac (Apple M3), native build of the same client source, single-threaded:
26.7 s (transfer) and 26.8 s (withdrawal), peak resident memory 0.61 GB. On the efficiency cores
at background priority: 154.6 s. In the runs above the prover ran in an emulated x86-64 container
(about 40 s per proof), and on the shared build host 46 s to 67 s. No phone or browser measurement
exists.

## What the two runs establish, and what they do not

Established, as fixture measurements on devnet: four payments (two transfers, two withdrawals) on
two fresh Pool states were each verified and settled in one transaction, between 1,308,068 and
1,321,318 compute units; changed proofs and replays were rejected without state change; each
payment took 18 transactions with one signature from the payer; everything a payment created
except its nullifier marker was closed and its rent returned.

Not established: a compute bound over all inputs (root-page rollover and a Pool with a long history
were not exercised; the smallest observed margin is 78,682); any soundness claim for this verifier
(the rows are stated in docs/research/future-version/SOUNDNESS-ROWS.md and are not proved); the
source correspondence of the changed kernels. The release target is unchanged and not yet
established.
