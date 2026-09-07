# V7 TxV1 public-devnet lifecycle attempt — 2026-09-07

Classification: **PUBLIC DEVNET FEATURE ACTIVE; BLOCKED BY IDENTITY/ARTIFACT**

This is not a finalized combined lifecycle measurement. Public devnet accepted the real setup transactions and proof-account upload, but the exact terminal TxV1 simulation failed the deployed verifier's compile-time Pool/Registry identity gate. The terminal wire was not submitted. `PUBLIC FINALIZED DEVNET LIFECYCLE COMPLETE` and `MAINNET READY` are both false.

## Authoritative feature state

The Solana Foundation upgrade page currently lists Testnet and Devnet as Active and Mainnet as Not activated. The canonical devnet endpoint is `https://api.devnet.solana.com`; Solana documents it as a rate-limited public test cluster whose tokens have no real value.

The independent on-chain probe recorded:

- genesis hash `EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG`;
- feature `txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL` owned by the Feature program;
- active encoding tag `1`, activation slot `492480000`;
- RPC `solana-core 4.3.0-beta.3`, runtime feature set `2409014235`.

Raw responses are under `results/v7-txv1-public-devnet-20260907/cluster/`.

## What finalized

All listed setup transactions were simulated before the identical signed wire was submitted and reached finalized commitment:

| Action | Bytes | Simulated CU | Landed CU | Finalized slot |
| --- | ---: | ---: | ---: | ---: |
| Registry V2 initialize | 519 | 112,159 | 112,159 | 494,613,596 |
| Registry V2 schedule pair-forest Tag-73 | 633 | 937,018 | 937,018 | 494,613,641 |
| Registry V2 activate | 388 | 20,388 | 20,388 | 494,613,726 |
| Registry V2 freeze | 355 | 11,008 | 11,008 | 494,613,783 |
| Pool initialize (master, eight lanes, vault) | 784 | 121,442 | 121,442 | 494,614,656 |
| Deposit to selected lane 7 | 651 | 634,287 | 634,287 | 494,614,701 |
| Global checkpoint | 581 | 694,284 | 694,284 | 494,614,742 |

The live adapter then derived the witness from Pool master `2av1xq3YR2vZKoJENUgb1SWxRsEgbPmtgdZZqfNxXcve`, all eight finalized lane accounts, retained checkpoint `91di8RBKgBYGVhTmXuKooeSH1ANni63udpf27GfkZ8RN`, and the exact frozen Registry V2 entry.

The production prover generated a genuine transfer proof from that live note:

- 30,824 proof bytes, SHA-256 `658b4ba8f184d593e3b21460b404c0adca92ef404a818144b8fb85b5844fc44b`;
- 31,512 payload bytes, SHA-256 `f3b904e45eb516e42e66e0cfc2c2ef02d77a243ea0ccef31950a7c8bb2eea5e2`;
- compact counter 2 under cutoff 20, 203 frontier nodes, PoW valid;
- one valid final work nonce tested;
- no deterministic fixture entropy, verifier bypass, or trusted result account;
- ASQ8 320 bytes, ASF8 1,880 bytes, expected ASR8 792 bytes;
- 1,553,393 ms full prover wall time on the Mac. This is the complete proof construction, not an isolated final-grind measurement.

The normal proof-account path submitted 35 independently blockhashed wires. Every wire simulated successfully, landed byte-identically, finalized, and had identical simulated/landed CU. The largest was 1,173 bytes. Proof account `E262aCRQtaQTMb2cFr2pbyfuyYk8Cj2iVfZy3S34HoHQ` was sealed under the new verifier; the payload hash matched byte-for-byte.

## Exact terminal result

The builder produced a genuine V1 wire:

- first byte `129` (`0x81`);
- 1,378 serialized bytes, below both 3,500 and 4,096;
- two instructions: one real HPKE ciphertext carrier and exactly one terminal Pool instruction;
- selected lane 7;
- signed-wire SHA-256 `e183bbd5abbe0b5edfeb2e5c64531a104783339df598effd532803c74e56d1b8`.

Simulation rejected at instruction 1 with `InvalidAccountData` after 57,181 total CU. The verifier consumed 5,632 CU before rejection. The candidate signature is evidence of the signed simulation wire only; it is not a landed signature. No send request was issued.

All non-payer Pool/lane/history/vault/marker/proof/Registry/program account values were byte-identical before and after the rejected simulation (SHA-256 `12caecda4a3bdfe106fa077a62feb886bd812a60c874fd029bb89bc5bc6bb0d0`). The shared local devnet payer changed by 10,000 lamports because two unrelated finalized transactions used it concurrently; those signatures and programs are outside this harness. This means the wallet-isolation requirement was not met after the task-owned NUC payer became unreachable, and the report does not claim it was.

## Smallest blocker

The deployed verifier was built with `v7-pair-forest-lane-invariant-audit`. Its source hard-codes:

- Pool program bytes `[0x41; 32]`, base58 `5PjDJaGfSPJj4tFzMRCiuuAasKg5n8dJKXKenhuwZexx`;
- Registry program bytes `[0x44; 32]`, base58 `5bV6jUfhDHCQVA1WfKBUnXUsboJgoKgkzkKcxr3joew5`;
- policy binding `[7; 32]`.

The immutable public-devnet test deployments are Pool `H93X…XpJYW` and Registry `CR1P…xpn8h`. Both compile-time audit addresses are absent on devnet. They cannot be populated without their signing keys. Therefore an otherwise valid freshly initialized Pool is rejected before cryptographic verification.

The smallest resolution is a verifier build whose invariant constants authenticate one deliberately selected immutable test Pool/Registry identity set, followed by deployment and a fresh proof. That is verifier production-source/release work and was explicitly outside this task. Binary patching, bypassing authentication, or pre-authorizing ASR8 would be unacceptable.

The harness now records these compile-time bindings and rejects the incompatible public-devnet config before account creation or proving. This prevents another expensive false-start.

## Matrix status

- Finalized: Registry lifecycle, Pool initialize, deposit, checkpoint, genuine live-note proof generation, complete sealed proof upload.
- Real but simulation-only: canonical same-page transfer TxV1, rejected by identity authentication and not submitted.
- Blocked behind the same gate: rollover transfer, both withdrawals, different lanes, stale lane, replay, wrong checkpoint/release, malformed ASQ8/ASR8/carrier, missing carrier, failed withdrawal CPI rollback.
- Proof close/refund: not completed. The fail-closed runner destroyed the task proof key after terminal simulation failure, so the sealed proof account cannot satisfy the close instruction's proof-signature requirement. No secret was printed or committed.

The frozen 997-byte / 1,201,757-CU combined measurement was not rebuilt, rerun, added to this simulation, or represented as public-devnet execution.

## Tooling and resource record

- SBF deployments were built with pinned Agave 4.2.0 on the dedicated Linux host under `MemoryHigh=8G`, `MemoryMax=12G`, `MemorySwapMax=0`.
- Local terminal builder used `solana-message 4.2.4` and `solana-transaction 4.1.5`.
- Local CLI was Solana 2.3.0; public RPC was 4.3.0-beta.3.
- Full lifecycle parent peak RSS: 195,903,488 bytes, zero swap.
- Focused Registry test: 15.35 s, 758,054,912 bytes peak RSS, zero swap, 1 passed and 121 filtered.
- Focused uploader release rebuild: 1.91 s, 225,148,928 bytes peak RSS, zero swap.
- No broad regression, frozen CU profiling, Lean/Aeneas replay, or post-deployment SBF rebuild was run.

## Revisions and safety

- Tested base: `0f54ffe4d12dd82331951e8a9f3d2857de9aef29`.
- Harness milestone: `9604f01d`.
- Program source commit embedded in the config: `bff78d6eab006dfc75c704abde824fa7c57637b1`.
- Branch: `research/v7-all-reachable-cu-bound-testnet-20260902`.
- All deployments are public-devnet-test-only and immutable. No production identity was selected. `mainnetReady` is explicitly false.

The harness/tooling changes are safe to cherry-pick. The devnet config and evidence are research-only and should not be interpreted as a deployable production identity set.
