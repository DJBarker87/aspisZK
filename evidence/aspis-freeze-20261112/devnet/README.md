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
| frzlocal3 | the frozen artifacts of this deployment | started before the devnet run; result below when it finishes |

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

## Results

(to be filled in after the run)
