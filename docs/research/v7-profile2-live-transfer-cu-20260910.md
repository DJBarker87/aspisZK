# V7 profile-revision-2 live transfer CU measurement

Date: 2026-09-10  
Source revision: `c4285d7e767851a72a0ef11c13d59df51416ca9a`  
Classification: **genuine local disposable TxV1-active lifecycle evidence; not
public-devnet or mainnet readiness evidence.**

## Result

The current Tag-73 profile revision completed a genuine live eight-lane Pool
private transfer in one terminal transaction on a disposable Agave 4.2.2
validator with TxV1 active at genesis.

| Item | Result |
|---|---:|
| Honest proof body | 30,616 bytes |
| Honest proof payload | 31,304 bytes |
| Final terminal wire | 1,378 bytes |
| Terminal simulation | 1,158,165 CU |
| Byte-identical finalized terminal | 1,158,165 CU |
| Margin to 1,300,000 CU | 141,835 CU |
| Margin to 1,200,000 CU | 41,835 CU |
| Finalized slot | 622 |

The original terminal wire SHA-256 was
`e3fcd7871dfbcd9e6c19f3fd6c04b06516bc96dde2a8670fd50a50fb2510c5ee`.
The honest proof body SHA-256 was
`63b96af0aef898a4e079b1c8702e2f6629a37ff8f250a6ce84ef3b9d1db42b7c`.

The byte-identical replay was rejected as `AlreadyProcessed` before consuming
CU. A fresh-signed duplicate reached the nullifier gate and failed with the
expected custom error after 31,822 CU. The lifecycle harness's account-image
checks passed and its complete checksum manifest verified.

## Exact build inputs

The Pool and verifier SBF artifacts were rebuilt from the source revision
above with the default-off `v7-pair-forest-one-tx-candidate` feature:

```sh
NO_DNA=1 cargo build-sbf --manifest-path programs/aspis-pool/Cargo.toml \
  --no-default-features --features v7-pair-forest-one-tx-candidate
NO_DNA=1 cargo build-sbf --manifest-path programs/aspis-verifier/Cargo.toml \
  --no-default-features --features v7-pair-forest-one-tx-candidate
```

The corresponding artifact digests were:

| Artifact | SHA-256 |
|---|---|
| `aspis_pool.so` | `9cd1401327493134ca42ed13a7e72d7e6c375c488f7aa2ede42b39f402b6c89d` |
| `aspis_verifier.so` | `af9f8abb9639d25f624f970e021a518bdcfcbdd99aeb75fb61d3075db648e294` |

The host lifecycle tools were built with:

```sh
NO_DNA=1 CARGO_BUILD_JOBS=2 cargo build --release --locked --offline \
  --manifest-path tools/v7-live-pool-proof/Cargo.toml
```

All three builds and the live lifecycle were constrained through the NUC's
Tailscale connection with `MemoryHigh=8G`, `MemoryMax=10G`, and no swap. The
live lifecycle peak remained below 2.4 GiB.

## Scope and remaining gates

This replaces neither an all-reachable counter bound nor public devnet
evidence. It establishes a current-profile, real combined transfer measurement
only. The current formal K1.3 adversary-first parsed-profile causality endpoint,
K1.4/K1.5 composition, full release/source composition, an all-reachable CU
bound, and public TxV1 devnet activation/lifecycle are still open.

The first run was deliberately stopped during setup because its explicit
provenance environment value had a typo. It produced no terminal transaction;
only the corrected run reported here is authoritative.
