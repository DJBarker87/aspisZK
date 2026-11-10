# NPC_ B2 result: frozen verifier and frozen Pool on a local validator

The pinned verifier ELF 63ad3e9c and the frozen Pool ELF e0e49c34 ran together on a local Agave 4.2.0 test validator. Both the honest transfer and the honest withdrawal settled through TX1 (verifier) and TX2 (Pool). Both replays were rejected with NullifierAlreadyConsumed. Both mutated stage-1 proofs were rejected with InvalidInstructionData, and both proofs were restored. Every one of the 69 transactions has a full recording. This is local operational evidence. It is not a devnet run and not a soundness theorem.

## What was loaded

The validator cloned the devnet feature set and three devnet programs by read-only RPC: the registry 9pWwAc... (7ad46f0d, immutable), the carrier 3jEFrv... (9d45bbcb), and the verifier CSnhzGdH... It loaded the Pool program BmsNik... from the frozen ELF rebuilt in Phase 1, with upgrade authority Xjb7roDV... as on devnet (a public key only; nobody holds the key). The preflight (out/NPC_local-preflight.json) read each program's ProgramData back at finalized commitment:

| Program | Address | Payload | Authority |
| --- | --- | --- | --- |
| Verifier | CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ | 1,563,728 bytes, SHA256 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299, no padding | none (immutable) |
| Pool | BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs | 345,648 bytes, SHA256 e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc, no padding | Xjb7roDV... |
| Registry | 9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q | 209,280 bytes, 7ad46f0d... | none |
| Carrier | 3jEFrv5Npn3RmFMW1Cbzq5yEiLdeFB5vbBGmnfoqK9vN | 20,136 bytes, 9d45bbcb... | Xjb7roDV... |

The local Pool ProgramData is sized to the ELF (345,648 bytes). On devnet, BmsNik's ProgramData is 605,704 bytes. The registry hashes only the verifier's ProgramData, so this does not enter any check. It is a difference from devnet all the same.

## Sequence and results

The driver is NDZ's r1_devnet_spend.py with three changes (local/NPC_spend.diff): an import, the recording hook, and an upload worker count. The count was set to 1, so each upload had an exact pre-state; that changes only pacing. NDZ's four helper modules were used byte for byte; their hashes are in out/NPC_spend-receipt.json. All keys are fresh, local-only, namespace NPC, on the build host. Proofs were generated fresh by NDZ's pinned native client (devnet_spend, SHA256 77e7e541...); the proof cache was not reused.

Order: mint, source and destination token accounts, supply 2000. Registry initialize, schedule (verifier CSnhzGdH, hash 63ad3e9c), activate, freeze. Pool initialize (AS8I) into master GanWKFe73KPW2kTfEJfXkEFAVGrVQDKV7fVCTrg83EQ8, registry E3SeyvjQfk5gMdoG1UHipWezxL5VSH2Ra4odqVzUJFhj, entry CTBkdziFm4KtU63oWykmgjMWXEodwhG2UK451dfDhxuP, vault JBNGRop8yzxVXRRDarCDqVojZHCD6ubZvS143k1Qoydu. Two deposits (AS8D) and a forest checkpoint (AS8C). Then, for the transfer and then the withdrawal: 16 proof uploads and 1 statement upload to the carrier, verifier checkpoint creation, stage 1, stage 2, replay, a fresh negative checkpoint, proof mutation, mutated stage 1, and proof restore.

| Step | Program/magic | CU | Result | Local signature |
| --- | --- | ---: | --- | --- |
| pool-initialize | Pool AS8I | 127,374 | ok | T4bYhTEAmwPQGVnyza9KPKE7VMub3tUpXrN7d9A8fjBTzFJfq9wTeduhytFb5uitir5RWhEBare7j3qgwUmDiHb |
| deposit-0 | Pool AS8D | 1,105,471 | ok | 48SGaDPrDoLHzeHwK5JBXBtynGgoFHVpjU8e1qzgiFu3SGfDmpp8jPkwn9D96pa4c3tL6UZSkLS3p6As3ZFtVaqm |
| deposit-1 | Pool AS8D | 1,103,966 | ok | 5VHw7Pdix6SNVaYX2aSoVnFvAAP8KG3CXumzKMLfD8N53sYLyjyzpUCo3WwugEGQDWt8VcYsELtDQTQXUbwUxZLk |
| forest-checkpoint | Pool AS8C | 1,158,427 | ok | 4NtAzH9RVh5rveRFZqZXzpyxkpfECfPkvwW3tGhiHRihUkQMT37CUR56m6Frh84gDL4Tur1DfcoiboxbGM9BF9WA |
| transfer-stage1 (TX1) | Verifier | 1,213,142 | ok | 25jeRJ8KzNHmTAkg3gu7GrYkwCtnQFmDK1k558cVmWAc9y6mRPCF8xKRG7EuV5CDdkwzvqs8owsSKHu8N4dZp7vK |
| transfer-stage2 (TX2) | Pool ASQ8 | 1,141,779 | ok; vault 2000, destination 0 | 668mKkZsQc1wGwUF2iSE5oiUAucMyFE2vhyarkMo4gBbDzb2vSe4z1VX5aLkkbqWmgi9Hsobwm9xnHgTLLL3CF5p |
| transfer-replay | Pool ASQ8 | 67,240 | Custom 0x41532026 (NullifierAlreadyConsumed); protected accounts unchanged | 2CkznsB4LmUgm28FCYZTUrPASqnQ9Z6BqGg1y3esXqEGwhtVwotqP3Uwt6bx2W3HBfM94od6wh7s3Dr2XHjLsSdM |
| transfer-mutated-stage1 | Verifier | 21,453 | InvalidInstructionData; fresh checkpoint unchanged | 4C8EEdj71c4Km4qyT38mHT434JPaiVpnpGi92A8jd3swRbh2PPvpe3CS8rAUj2BnxW4dTkk995QkbiLtLJqrFpZq |
| withdrawal-stage1 (TX1) | Verifier | 1,205,067 | ok | 61dNXEYmJATxZJf4uXKBfamSwQnoFD6YMReFG45U53jGUrk9yzpuKppDgvnCJ138Baj517qskQ82HLWvbBs4En8a |
| withdrawal-stage2 (TX2) | Pool ASQ8 | 1,147,429 | ok; vault 1750, destination 250 | 3hB9vh67A8FUtEHj3KSyj2SU8u2Gzc36S5TYrScbT5C7f7KnidFq2X8Fh93N1k1PXGnB7ci3ktUT2rgH2DvUVTCo |
| withdrawal-replay | Pool ASQ8 | 68,841 | Custom 0x41532026; protected accounts unchanged | 3Fe7FXHhTrsh1JBhKraPxePB19dWGx3u4XLamybqbAK6yR2K4KHAYZJhc63Ye3dgLUVS3tBQ1bMWJ4FevLkEE3Hh |
| withdrawal-mutated-stage1 | Verifier | 21,395 | InvalidInstructionData; fresh checkpoint unchanged | Xrhacsh1Zj8ieYgx5f1rN9hiwn8Quh4nor8DuGVF7z96zWnbToVUCqVn18qkoVoLnkn5XAVJGuxTVTpGfFu4pTJ |

The mutation flips the low bit of the compact proof header byte at offset 688 of the 58,295-byte proof account (len - 57,607), leaving the candidate bytes intact. The restore writes the original byte back. Stage 2 returned the ASR8 result through Program return in both settlements. complete.json records both settlements and all four negative checks. All 69 signatures, with slot, CU, fee and error, are in out/NPC_LOCAL_SUMMARY.json.

## Recording

out/NPC_LOCAL_TRANSACTIONS.json.xz (722,312 bytes; SHA256 b2d87d69be4cee8e93c0b358d1614354181b7b66b8e12b38c18bfaa0c09b773a; decompressed JSON SHA256 3b8af292d728e81f2b718367408ade7613d7a2d94f5d0101dfbb7d4198d0edf5) holds every transaction in order. Each record contains:

- the signed serialized transaction bytes, and each instruction's program, account metas (key, signer, writable) and exact data;
- the signer/writable flags derived from the landed message header (checked equal to the instruction key set; no lookup tables);
- full account images (owner, lamports, executable, rent epoch, data) of every account the transaction names. The pre-image is taken after signing and before submission; the post-image is taken at finalized commitment after landing;
- an isolation check over every writable account: no other signature touched it between the two image slots. It held for all 69 transactions;
- the Clock slot (the bank slot) and blockTime (the bank Clock's unix_timestamp), plus the epoch schedule;
- the finalized getTransaction in json and jsonParsed encodings: logs, inner instructions, return data, CU, fee, error, and pre/post lamport and token balances.

The proof and statement bytes are the carrier accounts' data in the stage-1 pre-images (58,295 and 1,880 bytes per spend). They are also checked by the driver's full readback against the client's proof files.

Not captured: syscall-level replies (sol_sha256 inputs and digests, create_program_address results, get_clock values). The test validator and its RPC do not expose them. The pinned runtime's own single-instruction replay tool also fails. `agave-ledger-tool program run` in Agave 4.2.0 exits during argument parsing ("The argument 'accounts_index_limit' wasn't found") before executing anything; see out/replaytest/. For a later replay, out/NPC_REPLAY.tar.xz has a `program run` input for every Pool, verifier and registry instruction (16 files). Each is built from the exact pre-images: program id, accounts in instruction order with signer/writable flags, lamports, owner and data, and the instruction data. The recipe:

`agave-ledger-tool program run -l <ledger with this run's genesis> --mode interpreter --trace <file> -i <input>.json <ELF>`

Use pool.so for Pool instructions and the 63ad3e9c ELF for verifier instructions, under an agave-ledger-tool version whose `program run` works. That mocked environment does not reproduce CPIs or the bank's Clock, so it reproduces only CPI-free single-program executions. The retained ledger (keys/NPC_ledger on the build host, 6.5 GB) holds every block of this run for full-transaction replay.

## Accounting

The payer started at 18.353204080 SOL (genesis account) and ended at 17.267477360 SOL. The recorded pre/post payer deltas sum to -1.085726720 SOL, which equals the balance change exactly. That is 28 newly funded accounts, 1.084416720 SOL (out/NPC_spend_receipts.tar.xz, rent-ledger.json), plus 0.001310000 SOL in fees. Total CU over the 69 transactions is 9,350,581.

## Resources

| Target | Exit | Wall | Peak RSS | Cgroup peak | Swap |
| --- | --- | ---: | ---: | ---: | ---: |
| Validator (service, 6G high/8G max, swap 0, 512 tasks) | 130 = intentional SIGINT; time exit 0 | 3:51:45 | 1,510,432 KiB | 6,443,298,816 bytes (page cache held at MemoryHigh; no OOM) | 0 |
| Spend (3G high/4G max, swap 0, 256 tasks) | 0 | 1,207.19 s | 550,472 KiB | 605,102,080 bytes | 0 |
| Collector (unscoped; read-only RPC and file aggregation) | 0 | 2.44 s | 250,016 KiB | n/a | 0 |

Deviation: the spend scope was capped at 3G/4G, not the 6G/8G in the instruction. The host's reservation gate refused 8 GiB (51.4 GB reserved, 60.0 GB projected against a 59.1 GB safe limit; out/spend-refusal1.json), so nothing launched at that size. 4 GiB was admitted. NDZ's proof-generating spend peaked at 582 MB under the same 3G/4G cap. The validator's resource JSON writer failed on a timestamp with spaces; the systemd accounting is in out/NPC_validator-systemd-show.txt and GNU time in out/NPC_validator.time. `#print axioms`: N/A, no Lean target.

## Runtime caveat

The local runtime is Agave 4.2.0 (src ac82b5d4, feat 21b0d33a), with devnet's active features cloned at genesis. Devnet runs 4.4.0, and this run does not establish runtime equivalence. The local genesis rent is 6,960 lamports per byte against devnet's 5,080, so the rent figures are higher than devnet's. The RPC, finality and loader behaviour remain trusted as before. No premise was discharged, added or changed.

Target not yet established.
