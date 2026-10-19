# Release bundles

Frozen release inputs and finalized public records. Each bundle carries its
own manifest, `SHA256SUMS` and, where applicable, an offline `verify.sh`.
Files here are referenced by hash and path from those manifests, so they are
not moved or edited after release.

| Bundle | Contents |
| --- | --- |
| `aspis-v5-tag67-mainnet-v1/` | Finalized V5 mainnet transaction and cleanup |
| `aspis-v5-tag67-frozen-candidate-v1/` | Frozen V5 program and build inputs |
| `aspis-v5-tag67-mainnet-rpc-archive-v1/` | RPC archive of the V5 mainnet lifecycle |
| `aspis-spend-q18-g37-mainnet-v1/` | Earlier q18/g37 feasibility transaction |
| `v7-one-tx-candidate-preflight-v1/` | V7 one-transaction release-candidate preflight |
| `v7-registry-v2-mainnet-rc1/`, `v7-registry-v2-runtime-audit-v1/` | V7 registry release candidate and runtime audit |
| `v7-agave-v4.2.0-runtime-v1/` | V7 runtime record on Agave 4.2.0 |
| `preflight/` | V5 production freeze and pre-mainnet test records |

`release-facts.json` holds the canonical public figures, checked by
`../tools/check_release_facts.py`.
