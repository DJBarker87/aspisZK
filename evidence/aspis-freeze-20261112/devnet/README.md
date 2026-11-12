# Aspis one-transaction verifier, frozen source: devnet deployment and run (12 November 2026)

A test deployment. No security claim is made by it: the release target is not established
(docs/research/future-version/ASPIS-FREEZE.md).

## What is deployed

| Item | Value |
|---|---|
| Source | commit 3d700effcab (`crates/`, `programs/`, `tools/`) |
| Verifier program | 8EEVxFAXz9BSg5LKaBxRfTbSK5xZyFrshLfKQRASvvNC, ProgramData AR6y2GJdo9E4eoDJss4fDD4Z5s6Pn3EegdoursjQtx27, upgrade authority none, deployed in slot 521354053 |
| Verifier ELF | sha256 6f53dc5a923ad2beecc9ee11f59ce2f1c16ac388a82a5cfcd7855f31994d5890, 969,328 bytes (the frozen source built with the new Pool's address embedded) |
| Verifier deploy signature | 257VNU56ThQ8bUdBHfbDYuAtpcpKaXyHoZSdJKaXf9sKWcgGvgk3VseVRGTtie6fMiGANwXCyPPt71CfWPVP1xwi |
| Pool program (new) | 4hxEyoU8MC3oFMya8D8MAcvhCPhLfHKDP1Ji9byYycn1, ProgramData HQYymGASjX7GnpDZLmQ1qPdE2KWYB29St84UVqMPrsxH, upgrade authority the payer, deployed in slot 521353809 |
| Pool ELF | sha256 0553a8bd5ef5c5ff93023b1923f96f9651a23f5aa4e50855baebe29109799cec, 340,320 bytes |
| Pool deploy signature | 5AkzpXgKugE4kWNuuCPRCGigP8UA5tygyboWV2iCjTniWTHwsdaoRef9PQvJb3Bnh6FS8vHg8rZmSJVTVLY1dKMv |
| Registry and upload programs | the deployed ones, unchanged: 9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q and 9DYn3ykkW6JEgYVKst7y7Jd9SqxSjoSNUVTgnGCHWqx5 |
| Client binary `devnet_spend` | sha256 ca84d10ac7c6bdb9a6182bbc40820bbca16870fecff54bb500dd228641ad4715 (frozen source, feature `r1p-check`, Rust 1.94.1, built on the build host) |
| Payer | CVZJcAv97von8njTJSyLVQ9X33NAKQYbEXFKnAYvst9t: 25.616580781 SOL before, 23.884238577 after the Pool, 18.953238048 after the verifier |

The Pool is a new program. The Pool at 37hdATMk…, which the two-transaction run of 11 November
uses, is not touched.

Rent. Verifier: 4,925,065,080 lamports in ProgramData, permanent (the registry accepts a verifier
only with its upgrade authority revoked). Pool: 1,729,704,440 lamports in ProgramData, recoverable
by `solana program close` with the payer key while the authority is kept. No buffer account is
left (deploy/buffers-after-deploy.txt).

Keys: payer ~/.config/solana/aspis-deploy/devnet-payer-20261029.json; program and buffer keypairs
~/.config/solana/aspis-deploy/ASPIS-20261112; run keys ~/.config/solana/aspis-deploy/ASPIS_onetx-20261112.
None is in the repository.

Preflight after the deployments (deploy/ASPIS_PREFLIGHT.json): deployed payloads equal the four
ELFs, verifier, registry and upload program immutable, TxV1 active, funding passes.

## What is run

`ASPIS_spend.py`: the run script of the earlier one-transaction run (FV_spend.py of
evidence/future-version-20261111/devnet) with one addition, three redirect attempts before the
withdrawal settles. Fresh mint, registry entry for the new verifier, fresh Pool state under the
new Pool program, two deposits, forest checkpoint, then a private transfer and a withdrawal, each
verified and settled in one transaction. Per payment: open (signed by the payer, funds a session
key), 15 proof writes, the settlement, the close. Tests that are not part of a payment: a changed
certificate byte and a changed Merkle node byte before each settlement, a replay after it, and for
the withdrawal the destination replaced by another token account of the same mint and owner (in
the request and the account list; in the account list only; in the request only).

## Rehearsals on a local validator (build host, Agave 4.2.0, devnet feature set, registry and upload program cloned, new Pool ELF at the new address)

| Run | Artifacts | Result |
|---|---|---|
| frzlocal1 | candidate verifier with the new Pool address, candidate client, the host's old copy of the run script | Pool initialize, two deposits and the forest checkpoint ran; the old script then stopped at its check of the earlier proof-format label. Not a program failure |
| frzlocal2 | same programs, current run scripts, `ASPIS_spend.py` | complete: transfer settled at 1,229,162, withdrawal at 1,241,646; changed certificate rejected after 1,018,608 and 1,024,057, changed node after 1,087,555 and 1,094,263; redirect in request and accounts rejected (InvalidInstructionData) after 132,167, in the accounts only and in the request only (Custom 1095966770) after 22,276; replays rejected; closes and cleanup returned the rent |
| frzlocal3 | the frozen artifacts of this deployment | complete, but it finished at 05:38 UTC, after the devnet run (it waited for host slots): transfer settled at 1,230,648, withdrawal at 1,241,664; changed certificate rejected after 1,018,560 and 1,024,143, changed node after 1,088,035 and 1,094,317; the three redirect attempts and the replays rejected as in frzlocal2 |

## Predictions for the devnet run (registered before its first signature)

1. Both settlements succeed in one transaction. computeUnitsConsumed is in [1,224,000, 1,240,000]
   for the transfer and in [1,236,000, 1,250,000] for the withdrawal.
2. Changed certificate byte: InstructionError [0, InvalidInstructionData] after 1,010,000 to
   1,035,000 compute units. Changed Merkle node byte: the same error after 1,078,000 to 1,104,000.
   Replay: InstructionError [0, Custom 0x41532026]. No protected account changes in any of them.
3. Redirect attempts on the withdrawal: request and accounts, InvalidInstructionData after 125,000
   to 140,000; accounts only and request only, Custom 1095966770 after 20,000 to 25,000. Neither
   token account and no protected account changes.
4. Each payment is 18 transactions without the tests; the payer signs exactly one of them; the fee
   is 20,000 lamports for the open and 15,000 for every other.
5. The payer's balance falls by 2,086,880 lamports for the transfer and 2,131,880 for the
   withdrawal (1,706,880 marker rent each; fees 380,000 and 425,000 with seven and ten test
   transactions). The session key, the proof account and the checkpoint account do not exist
   afterwards.
6. The cleanup returns 2,976,880 lamports from the two fixture token accounts.
7. The payer ends between 18.814 and 18.818 SOL.
8. The 15 writes are confirmed within 15 seconds of the first send and none is re-sent. This one
   depends on the public endpoint and is the least certain.

## Results of the registered run (devnet, 12 November 2026, 05:16 to 05:28 UTC)

Receipts: `receipts/ASPIS_spend` (70 recorded transactions and the cleanup), logs
`receipts/ASPIS_spend.log` and `receipts/ASPIS_cleanup.log`. The run was not interrupted and
nothing was re-sent. Predictions were committed at 9f8500f42a6 before the first signature.

| Prediction | Result |
|---|---|
| 1. Transfer settles in one transaction, 1,224,000 to 1,240,000 | Settled at 1,234,048. Met. 165,952 under the limit of 1,400,000. |
| 1. Withdrawal settles in one transaction, 1,236,000 to 1,250,000 | Settled at 1,238,634. Met. 161,366 under the limit. |
| 2. Changed certificate byte rejected, 1,010,000 to 1,035,000 | InvalidInstructionData after 1,018,609 and 1,023,962. Met. |
| 2. Changed node byte rejected, 1,078,000 to 1,104,000 | InvalidInstructionData after 1,089,131 and 1,093,217. Met. |
| 2. Replay rejected, protected accounts unchanged | Custom 0x41532026 both times, accounts unchanged. Met. |
| 3. Redirect in the request and the accounts rejected, 125,000 to 140,000 | InvalidInstructionData after 132,167; no protected account and neither token account changed. Met. |
| 3. Redirect in the accounts only, and in the request only, rejected, 20,000 to 25,000 | Custom 1095966770 after 22,276 each; nothing changed. Met. |
| 4. 18 transactions per payment, payer signs one, fees 20,000 and 15,000 | Met for both payments. |
| 5. Payer balance change 2,086,880 (transfer) and 2,131,880 (withdrawal) | 2,086,880 and 2,131,880. Session key, proof account and checkpoint account gone. Met. |
| 6. Cleanup returns 2,976,880 lamports | 2,976,880. Met. |
| 7. Payer ends between 18.814 and 18.818 SOL | 18.816106048 SOL. Met. The run cost 137,132,000 lamports outside the deployments. |
| 8. 15 writes confirmed within 15 s, none re-sent | 10.69 s and 10.70 s, none re-sent, 15 different slots each time. Met; the figure measures this script, which spaces its calls. |

Settlement transactions:
transfer 2UN82ys58uXKAWWRovbYpxb4mp8nrPKNkZE5ViCR24ugcW7jfKeqEcYQT742Gs5zqrcr6VoqRsfJMGYqtpZCzcht (slot 521356085),
withdrawal 2x4Hy6bA8wcEMHHtYiv98RRvUi73aT2YZpfojbnba3jT1NvRMNiHwHnqRxcnnTiL6pXbBmGwhLGci4kFLfmyCa8J (slot 521357198).

Other transactions of the run with the new Pool: Pool initialize 96,504 compute units, deposits
1,067,235 and 1,064,230, forest checkpoint 1,152,988. The Pool's changed page check ran on the
cluster in the initialize (it validates the new root page accounts as zeroed).

What stays spent: the two nullifier markers (1,706,880 lamports each, permanent by design), the
Pool state for the new mint, the registry entry, the mint and vault (no close path in these
programs; `receipts/ASPIS_spend/rent-ledger.json`), and the fees. Everything a payment creates
besides its marker was closed by that payment.

Two labels in the receipts are the unchanged script's and are not corrected: `complete.json`
names the route by its earlier experiment label, and its `negative_checks` list does not name the
three redirect attempts, which are in `withdrawal-redirect-validation.json` and in the
transaction records.

The rehearsal with the frozen artifacts (frzlocal3) was still waiting for host slots when the
devnet run started and finished after it; its result is in the table above.

These are test transactions on a test cluster with fixture witnesses. They show that this build
verifies and settles these two payments in one transaction each and rejects these nine altered
attempts. They are not evidence of soundness.
