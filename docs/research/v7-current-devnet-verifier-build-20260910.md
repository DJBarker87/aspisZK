# V7 current-profile public-devnet verifier build — 2026-09-10

## Scope

This is a reproducible, build-only checkpoint for the current V7 Profile-2
source. It restores the explicit default-off public-devnet identity capability
needed to authenticate the immutable V7 Pool and Registry deployments already
used by the finalized 2026-09-07 public-devnet transfer and withdrawal.

It is not a deployment, transaction submission, or a claim that the current
release has completed the public-devnet lifecycle.

## Frozen source and artifact

- Source revision: `573e0a263a4aa90675e3c376547a8495c22747bb`.
- Verifier features:
  `v7-pair-forest-one-tx-candidate,v7-pair-forest-public-devnet-identity-audit`.
- SBF artifact: `aspis_verifier.so`.
- Bytes: `2,085,368`.
- SHA-256:
  `32cdfe5ff67776875f2efa8b065d9ef8cbdae91687866e1b12e996375f2923f8`.

The devnet identity capability is explicitly opt-in and is not included by the
one-transaction candidate alias. It substitutes only these two authenticated
program identities:

- Pool: `H93Xdk81pavjXwmNBSFeDbfndBxpyD3X43Bp7P2XpJYW`.
- Registry V2: `CR1PE8CVHdqkfPwSDGQUph22AK23n5S9wciZvdYxpn8h`.

The transcript, proof relation, request/result binding, Registry validation,
and Pool CPI order are unchanged by this build capability.

## Build evidence

The build ran on the NUC through Tailscale in the task-owned worktree
`/home/dombarker/project-offloads/aspis-v7-devnet-current-573e0a26`, using
Solana `cargo-build-sbf 2.3.0`, platform tools `v1.48`, offline dependencies,
and two build jobs:

```sh
cargo-build-sbf --offline --skip-tools-install -j 2 \
  --manifest-path programs/aspis-verifier/Cargo.toml \
  --features v7-pair-forest-one-tx-candidate \
             v7-pair-forest-public-devnet-identity-audit \
  --sbf-out-dir out
```

The systemd scope used `MemoryHigh=7G`, `MemoryMax=9G`, and
`MemorySwapMax=0`. It completed in 58.30 seconds with 570,676 KiB peak RSS,
zero swap, and exit status zero.

The focused identity test passed:

```sh
cargo test -p aspis-verifier \
  --features v7-pair-forest-one-tx-candidate,\
v7-pair-forest-public-devnet-identity-audit \
  public_devnet_identity_capability_is_exact
```

## Next runtime gate

Before any current-release lifecycle claim, deploy this exact immutable
verifier artifact to a new public-devnet test identity, authenticate its
on-chain bytes, bind a fresh Registry entry and live Pool state, then generate
and settle fresh transfer and withdrawal proofs. The earlier immutable
verifier remains valid historical evidence but has a different binary hash.
