# The R1 devnet run, 29 October 2026

Source: research commit `07123926e88273271344977a3fdc26d1780cde14`, directory `evidence/devnet-rehearse-20261029/`. The figures below come from `NDZ_DEVNET_RESULT.md` and the receipts in `NDZ_devnet_receipts/` (in particular `NDZ_IMMUTABLE.json`, `NDZ_ASSOCIATION.json`, `NDZ_spend/complete.json` and the per-transaction files in `NDZ_spend/`). Every signature can be checked on a public devnet explorer.

On 29 October 2026 the release R1 verifier was deployed to Solana devnet as a new immutable program and used to settle one private transfer and one withdrawal, each through the two-transaction path: the first transaction runs stage 1 of the verifier and writes a checkpoint account, and the second resumes from that checkpoint, completes verification and calls the Pool to settle. The deployed program is byte-for-byte the release ELF built from the frozen source, its upgrade authority is set to none, and a read-only check afterwards tied the live program, registry and Pool to that ELF. The owner approved the deployment on the condition that the whole procedure first be rehearsed on a local validator with cloned devnet programs and that the exact commands be reviewed before any devnet write; both were done, and the devnet steps were then run unmodified from the reviewed runbook.

## What was deployed

| Item | Value |
| --- | --- |
| Verifier program | `CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ` |
| Verifier ProgramData | `7GVKbnPt1XkYvnZURDLRKJqC89qbgfqP912hM3aUojRk` (upgrade authority none) |
| Verifier ELF | 1,563,728 bytes, SHA-256 `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`, written in 1,738 chunks and read back before finalisation |
| Pool program | `BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs` (existing program, ELF SHA-256 `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`) |
| Registry program | `9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q` (existing immutable program) |
| Fresh Pool state | `4GQ9Gnmi71ZonpVSJRsmRxyK2UMdVJJCXjYrbTetha1G` |
| Fresh registry | `CRqLcv1MfBq73gQ3unk7s7EArnUQqZvUbDdqTX8We2Pu`, frozen, with active entry `6Hd8P6negaxMLFqY3t1Q34PDwz32D8rD7qxkutP993V1` |
| Test mint and vault | mint `EhZ4nakdh7U1SivMhKjZy5XhYxHMNMXgmfZESa2RU5VM`, vault `4kjEXoJ7YdwgZJaome64VX8fyqNNbdVWXbCFB4LT3Eyu` |
| Cluster version | devnet RPC reported `4.4.0-beta.1` |

## What settled

| Operation | Signature | Slot | Compute units |
| --- | --- | ---: | ---: |
| Transfer, stage 1 | `53pTHDfJBmqX7hdxPofSfajURpMhCiB6ceAdMw9ftf3RAXZ6k8D26WaW4MGito2Ty3kRQrAXQSDJ5QBNFsm2hhvR` | 516453027 | 1,214,746 |
| Transfer, stage 2 and settlement | `FNLSBxjiJ8jPYzE2E25BCgzJ6rm9yrSXnRMgwhj3E5yxwU4wYPfs9vugucr6cVrgnhem2b6TbqPCe3PKjPRFCxF` | 516453041 | 1,145,305 |
| Withdrawal, stage 1 | `3C6fKwts7pAaTko8kJvBJk4weuUc9y7dfbLTGjRiKuqXo6fWr7xvNoG7w19Nb8V9yY6erAda5jt65khHY5ut4F7L` | 516453728 | 1,206,747 |
| Withdrawal, stage 2 and settlement | `46bYP2Bz1sTiwNDSFxYVumN1kPYa4TARupv8ptAMMx7ixwSNCZwU59WLNDz1zv5V97qgKFp6NtY4njs9rcES3wn2` | 516453751 | 1,154,975 |

All four transactions finalized without error. After the transfer the Pool's settlement record matched the expected lane and nullifier marker, and the vault held 2,000 test tokens with nothing at the destination; after the withdrawal the vault held 1,750 and the destination 250, which is the withdrawn amount.

## What was rejected

| Attempt | Signature | Slot | Compute units | Result |
| --- | --- | ---: | ---: | --- |
| Replay of the transfer's settlement | `dcqp7kp8sq4eeUejKRTPd71TMKkUEhhe8EkkAC29NtJ9PUvPcb3roJfwrs8n65VAPM7CvzwcSVYXs2Jn4S2Y3zN` | 516453080 | 67,251 | `Custom(0x41532026)`, NullifierAlreadyConsumed |
| Replay of the withdrawal's settlement | `La57ofw95VmBuBuFXx6iziBMdsMRnvMNtCX2ojg1mbhB7iuLmoQVrkucPNxBBpnqWqW4rNJHTWNbWTDXPzSzAPk` | 516453789 | 68,852 | `Custom(0x41532026)`, NullifierAlreadyConsumed |
| Transfer with a mutated stage-1 proof | `2N1EitRqZWRrDFWgSSUsKocjDDQQHaT2u4fgy3aobbE7cKgP9DKbRF7RCW2voJ1SQioa9F2eD7xmaR9ZpesgUSX9` | 516453172 | 21,453 | `InvalidInstructionData` |
| Withdrawal with a mutated stage-1 proof | `3DweqsyXeAXbQwefFRppjw1VUbXVjvSctz16oxU552GL5Q87A7G8co4JwwRptgK9EUFEt9cYo9ZbBtSsSkDv1czb` | 516453871 | 21,395 | `InvalidInstructionData` |

Each replay was rejected because its nullifier had already been consumed, and the receipts record that the protected accounts were unchanged; each mutated proof was rejected by stage 1, and the receipts record that the fresh checkpoint was unchanged. A final read-only check at finalized slot 516454111 confirmed that the Pool state was fresh, the registry was frozen with the release entry active, and the verifier's ProgramData was immutable and held the ELF with SHA-256 `63ad3e9c…4299`.

## What this run shows and what it does not

The run shows that the exact release ELF, built from the frozen source, runs on a public Solana cluster within the compute limit, settles a transfer and a withdrawal through its two transactions, and rejects a replayed nullifier and a mutated proof. It is operational evidence about the deployed artifact, and it closes the obligation to associate the release ELF with a live deployment for this devnet instance; it is not a soundness theorem, and the soundness argument does not rely on it.

Three limits should be read alongside it. The proofs were made for public test fixtures, so the run says nothing about privacy. The Pool program that ran on devnet is the build with ELF `121f3e29…1548`, which predates the removal of the legacy Pool instructions on 9 November 2026; the release Pool source on this branch (`programs/aspis-pool`, frozen at `b936275465600469312d1f058cdc91ea2a11f3dc`, ELF `e0e49c34…09dc`) has the same 427 pair-forest function bodies but a smaller dispatcher, and it has not yet been deployed. And the older Pool state on devnet, which still points at the historical verifier, was left untouched, so no continuity of its notes or custody is claimed. There is no mainnet deployment of R1.
