# NDQ chain association

Status: inventory frozen; live comparison pending. L188 obligation 5 is not yet closed.

Inspection revision: efdf060f90fb198006494e91d4a9f23a141a18d3.
Read `/Users/dominic/ZK/AGENTS.md`, including Security and proof discipline §6.
This task changes evidence only; it does not change release source, features or artifacts.

## Repository inventory

The public `config/r1-devnet.template.json`, `scripts/r1_devnet_spend.py`,
`scripts/r1_devnet_build.sh`, `design/DEPLOYMENT-IDS-IMPL-20261020.md` and
`docs/research/100bit-spend-path-20261013/evidence/devnet-r1-20261020/{README,REPORT}.md`
identify this devnet route at `https://api.devnet.solana.com`:

| Role | Program ID | Cluster |
|---|---|---|
| R1 verifier | Gk16spfMwbZ1wK1B8Y8upLd7y2DDJQz73iZKU5GEVyBA | devnet |
| Pool | BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs | devnet |
| Registry | 9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q | devnet |
| Proof carrier | 3jEFrv5Npn3RmFMW1Cbzq5yEiLdeFB5vbBGmnfoqK9vN | devnet |

The build script exports `ASPIS_R1_POOL_PROGRAM_ID=BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs`
and `ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q`
for the devnet variant. Unset defaults in `programs/r1-cost-probe/src/r1_pool_adapter.rs`
are byte arrays `[0x41;32]` and `[0x44;32]`, not evidence of deployment.
`programs/aspis-verifier/src/lib.rs` declares legacy ID
`7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue`; it is not the R1 cost-probe
verifier selected by the recorded spend route. No cluster deployment for that
legacy ID or the current default verifier artifact is established by these sources.
No mainnet deployment is recorded in the inspected release/deployment sources;
no mainnet query is authorized or planned.

Current ledger pins: default verifier
`f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`,
devnet verifier `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`,
Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.
The public devnet config instead pins historical verifier `fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78`
and default `dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34`.
These differing repository pins must not be silently identified.
