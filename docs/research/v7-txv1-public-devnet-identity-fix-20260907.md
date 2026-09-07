# V7 TxV1 public-devnet live transfer and withdrawal — 2026-09-07

## Result

**PUBLIC DEVNET FEATURE ACTIVE; LIVE TRANSFER AND WITHDRAWAL FINALIZED.**

This closes the smallest identity blocker recorded by the earlier
`v7-txv1-public-devnet-20260907.md` attempt. A newly built verifier with the
default-off public-devnet identity capability was deployed immutably, its
on-chain bytes matched the built artifact, and fresh live Pool deposits were
spent by genuine Tag-73 transfer and withdrawal proofs in V1 transactions on
canonical public Devnet.

This is not a mainnet release. The identities, Registry entries, mints, Pools
and transactions are public-devnet-test-only. The broader public negative-case
matrix and the all-reachable CU upper bound remain incomplete. Therefore:

| Classification | Established |
| --- | ---: |
| PUBLIC DEVNET FEATURE ACTIVE | yes |
| PUBLIC DEVNET LIVE TRANSFER FINALIZED | yes |
| PUBLIC DEVNET LIVE WITHDRAWAL FINALIZED | yes |
| PUBLIC FINALIZED DEVNET FULL LIFECYCLE MATRIX COMPLETE | no |
| ALL-REACHABLE CU BOUND ESTABLISHED | no |
| MAINNET READY | no |

Historical inactive-feature and identity-rejection evidence was not rewritten.
The raw successful run is under
`results/v7-txv1-public-devnet-identity-fix-20260907/public-devnet/`.

Branch: `research/v7-all-reachable-cu-bound-testnet-20260902`.

Identity-fix source revision:
`9a59478aaecc8b44a4e8cdbff92ae83157d57360`.

Tested harness revision:
`25bb8fda386b6abcbe496a769f2ff3774148478e`.

The final evidence commit is reported in the handoff because a commit cannot
contain its own hash.

## Cluster and feature authority

The canonical RPC was `https://api.devnet.solana.com`, and the observed
genesis hash was
`EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG`. The RPC reported
`solana-core 4.3.0-beta.3` and runtime feature set `2409014235`.

Feature `txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL` was present under
`Feature111111111111111111111111111111111111` with active encoding tag 1 and
activation slot 492,480,000, epoch 1140. This on-chain account—not the RPC
version string—was the harness authority. The Solana Foundation's canonical
[larger transaction status page](https://solana.com/upgrades/larger-transaction-sizes)
also lists Devnet and Testnet active and Mainnet not activated.

## Program and release identities

The public test programs are immutable Upgradeable Loader programs:

| Component | Program ID | Executable SHA-256 |
| --- | --- | --- |
| Pool | `H93Xdk81pavjXwmNBSFeDbfndBxpyD3X43Bp7P2XpJYW` | `9cd1401327493134ca42ed13a7e72d7e6c375c488f7aa2ede42b39f402b6c89d` |
| Registry V2 | `CR1PE8CVHdqkfPwSDGQUph22AK23n5S9wciZvdYxpn8h` | `0f14c7b74ec6cbe3b3f637b0f24c7e8cdc46fd09f5b2e495fd51ada16ad8f11b` |
| Identity-bound verifier | `CDeD7hL7MyvEv63VCw4T5Uv76Kn9ksYHYQXA3TzydVaq` | `5476d70d03fc3e55cee7bd3d7747023195713d0639afd9be66908e7ce09430c3` |

Verifier ProgramData is
`8kafJBYUo5yAYPmfS2JeqQYpuv1szL3Zq7d28bo2USNp`; upgrade authority is none.
Its deploy transaction finalized at slot 494,674,075 with signature
`3tiXCP4rJzdE3XdMKNMVy4RJDYXfHoB1eQbB7CekvtLzftzoGRSuhHjCQfJnEDarbiBL32L5gjDTXVWDofadJzux`.
An on-chain executable dump and the built SBF artifact have the same SHA-256.

The verifier was built with
`v7-pair-forest-one-tx-candidate,v7-pair-forest-public-devnet-identity-audit`.
The latter is default-off, is not included by the production-candidate alias,
and changes only the identity capability used for this immutable public test
deployment. It does not weaken proof acceptance or alter the Tag-73 relation,
proof format, transcript order, tree depth, TxV1 format or Pool CPI order.

Two independently created and frozen Registry V2 instances bound the exact
profile, release, policy, Pool, verifier and executable hashes:

| Operation | Registry | Entry | Registry/entry data SHA-256 |
| --- | --- | --- | --- |
| Transfer | `HiVkCHBCzVgtcPJgMZpb9GJ1d4FtEszS1mqfazQjzrym` | `8FobUuHA6RpFtVrmTEv6hH178cwrSB1YthNFohe1uL4e` | `5806a779…40b19b9` / `2f4e8276…91bfe29` |
| Withdrawal | `aPcpFRnpkTn6LUJBu2g7i5teLpXKMzHrkdq2f6BeRwT` | `8hrDGjkJodW2Fi3iZCJZ8Rx1Q2EfeuZMnkzLSeACycFF` | `22aef7e4…a0ac0562` / `0108f614…584fcb30` |

## Finalized live measurements

Every listed transaction was signed once, simulated with signature checking,
and submitted using the byte-identical base64 wire. The harness then waited
for finalized commitment and fetched the landed transaction with
`maxSupportedTransactionVersion: 1`.

| Case | Selected lane | V1 bytes | Simulated CU | Landed CU | Finalized slot |
| --- | ---: | ---: | ---: | ---: | ---: |
| Transfer terminal | 6 | 1,378 | 1,154,057 | 1,154,057 | 494,685,105 |
| Transfer fresh-signature replay rejection | 6 | 1,378 | 22,780 | 22,780 | 494,685,148 |
| Withdrawal terminal | 2 | 1,543 | 1,177,631 | 1,177,631 | 494,691,058 |
| Withdrawal fresh-signature replay rejection | 2 | 1,543 | 25,627 | 25,627 | 494,691,102 |

The successful transfer signature is
`61cevhjVRfBgsgXFfwB3shug2hYWdx53XNsjegjfcngySmjT1uEfJxvFqipeZLePn7xqiE5tXZFJqQSybBw9xNk5`;
its wire SHA-256 is
`46d8775f25955a77fadce3e1ef3b9489e543cadd706cf7009d90063450f784d6`.

The successful withdrawal signature is
`RwjVUtGX5158cQAkHP3CQn5V3MLg8nhkDS7EfgiuGjudHzPYvkvaznwTF6C1RmiYpQSdYcmBWYkczmUrSseyWJB`;
its wire SHA-256 is
`ffa923296925cbdd85677aabca521a443474d6ad5e88a8541b791fb2e169a329`.

Both wires begin with the V1 discriminator, contain one real canonical HPKE
ciphertext carrier followed by exactly one terminal Pool instruction, remain
below both 3,500 and 4,096 bytes, and land below the 1,300,000-CU measurement
gate. These are two concrete current-profile measurements, not an
all-reachable bound.

## Genuine proofs and state invariants

Both fixtures were new public-devnet Pools. Each path initialized the master,
all eight lanes and vault, finalized a deposit and retained checkpoint, decoded
the finalized live accounts, reconstructed the deposited note witness, and
called the production Tag-73 prover. No synthetic fixture entropy, copied
result, pre-authorized ASR8, verifier bypass or trusted result account was used.

| Proof | Proof bytes / SHA-256 | Payload bytes / SHA-256 | Counter | Frontier nodes | Full prover wall |
| --- | --- | --- | ---: | ---: | ---: |
| Transfer | 30,668 / `a893d43d…a9ab0ce6` | 31,356 / `19a55b9f…b6c9d044` | 1 | 200 | 141.541 s |
| Withdrawal | 30,616 / `20b31609…6348e14` | 31,304 / `6ef3e0cd…67584a2` | 0 | 199 | 368.953 s |

Both selected the first valid final work nonce and satisfied the default-off
counter-at-most-20 publication policy. Each proof used exact 320-byte ASQ8,
1,880-byte ASF8 and 792-byte expected ASR8 encodings. The sealed proof-account
path used 35 finalized upload transactions, and the terminal verifier accepted
the exact binding.

The post-state diffs establish:

- transfer changed only selected lane 6, its current history page and the new
  nullifier marker, apart from payer fee and marker rent;
- withdrawal changed only selected lane 2, its current history page, the new
  marker, authenticated vault and statement-bound destination, apart from
  payer fee and marker rent;
- both markers were absent before execution and became 208-byte Pool-owned
  accounts exactly once;
- master, retained checkpoint, sealed proof, Registry accounts and all seven
  non-selected lanes were byte-exact;
- withdrawal moved exactly 250 tokens: vault 1,000 to 750 and destination 0
  to 250; and
- both fresh-blockhash replay wires finalized as rejected transactions with
  matching simulated/landed errors and CU, while protected state was unchanged
  except the recorded 5,000-lamport fee.

Both proof accounts were subsequently closed through byte-identical simulated
and submitted 268-byte transactions at 782 CU. Transfer refunded 160,141,920
lamports; withdrawal refunded 159,877,760 lamports. The accounts were absent
after finalization.

## Why the proof was not 80 seconds

The approximately 80-second figure was not an end-to-end worst-case guarantee.
The public transfer proof took 141.541 seconds and the public withdrawal proof
took 368.953 seconds. The withdrawal selected counter 0 and tested exactly one
valid work nonce, so the extra time cannot be attributed to the counter-at-most-20
retry policy. It was built and executed as an optimized release binary, averaged
roughly 13 CPU cores across the encompassing run, stayed below 211 MiB parent
RSS and used no swap. The honest conclusion is that the current prover has
large full-proof latency variance outside the final counter selection. No
cryptographic work was skipped to force a faster result.

## Scope not closed

This public run establishes the positive same-page transfer and withdrawal,
finalized replay rejection and proof refund. It does not rerun rollover,
different-lane concurrency, stale-lane, wrong-checkpoint/release, malformed
ASQ8/ASR8/carrier, missing carrier or failed-withdrawal-CPI cases on public
Devnet. Existing disposable-cluster evidence for several of those cases stays
separate and is not relabelled as public evidence.

The source-level all-reachable CU audit still identifies unconstrained QM31
retry, query-ordering and PDA-search branches. These two successful counters
0 and 1 therefore do not prove that every reachable accepted transaction fits
under 1.3M or 1.4M CU. `mainnetReady` remains explicitly false.

## Focused commands and resources

The build host used dedicated systemd scopes with `MemoryHigh=8G`,
`MemoryMax=12G` and `MemorySwapMax=0`. The identity-bound SBF build took
56.48 seconds, peaked at 586,747,904 bytes RSS and recorded zero swap. The
complete transfer lifecycle took 308.20 seconds and the complete withdrawal
lifecycle took 541.98 seconds; parent peaks were 211,296 and 210,960 KiB,
respectively, with zero swap. No Lean/Aeneas replay, broad regression or
unrelated SBF build ran.

Replay commands, exact signed RPC requests, landed responses, program dumps,
account images, proof encodings, logs and checksums are in
`results/v7-txv1-public-devnet-identity-fix-20260907/`. The committed transfer
and withdrawal configs contain public identities only. `wallet-state.bin` and
all task keypairs are deliberately excluded.

The harness and builder changes are safe to cherry-pick as default-off test
plumbing. The public-devnet config/evidence and immutable deployments are
research artifacts, not production identity selection.
