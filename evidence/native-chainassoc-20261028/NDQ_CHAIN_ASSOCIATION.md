# NDQ chain association

**MISMATCH FIRST: the immutable devnet verifier loads
`fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78`,
not the current pinned devnet verifier
`63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`.
It also differs from the current default verifier pin `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`.
Pool matches the current release pin. No deployment of the current default verifier
is identified by the cited release sources. L188 obligation 5 remains OPEN;
target not yet established. Historical devnet success must not be attributed to
the current verifier artifact.**

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

## Finalized account observations

RPC window: `2026-10-28T22:36:31.385008+00:00` through `2026-10-28T22:36:47.988489+00:00`.
17 successful HTTP 200 / JSON-RPC reads: getVersion ×1, getSlot ×1,
getAccountInfo ×15 (four programs, four ProgramData accounts, seven named
feature accounts). No retries, scans, getProgramAccounts, cluster-node inventory,
transaction methods, signing, airdrops, wallet/key reads or chain writes.
All account reads requested `commitment=finalized`, `encoding=base64`.
Every raw request/response is retained; SHA-256 hashes, UTC start/end timestamps,
request parameters, source pins and decoded summaries are in
[NDQ_RPC_RECEIPTS.json](NDQ_RPC_RECEIPTS.json).

All four Program accounts are executable, owned by
`BPFLoaderUpgradeab1e11111111111111111111111`, and have a 36-byte Program-state
record (variant 2, then the linked 32-byte ProgramData address).
All linked ProgramData accounts have that same loader owner and variant 3.

| Role | ProgramData | Program read slot | ProgramData read slot S | Stored last deployment/upgrade slot | Upgrade authority A |
|---|---|---:|---:|---:|---|
| verifier | `4cKNG2KKxRcfSwEr1kTXJqWJQ5xLTc5w8eYraXSCYPRc` | 516207229 | 516207233 | 513171035 | none (immutable) |
| pool | `D7VhQ5FwMPE7CEGprZDjbmiYbdRBqWEJ8Ezid791BwxY` | 516207239 | 516207243 | 513173584 | `Xjb7roDVPDSPoZpUmDVUW5SMx21x7oQEg16dhb5TDXD` |
| registry | `2EFRxm3h3NAQqAebUjqmHgC1kFHwKyBJyGSJkCN4bQTg` | 516207247 | 516207251 | 513174495 | none (immutable) |
| carrier | `8MxXtWw84xJLnvSJZwR7dh3WhayaMykteGJFE8HYoU5s` | 516207255 | 516207259 | 513174657 | `Xjb7roDVPDSPoZpUmDVUW5SMx21x7oQEg16dhb5TDXD` |

The retained authority for Pool and carrier is the public address
`Xjb7roDVPDSPoZpUmDVUW5SMx21x7oQEg16dhb5TDXD`. No private material was accessed.
The slot encoded in ProgramData is the last modification/deployment slot, not a
claim that no previous program version ever existed.

| Role | ELF bytes | Loaded/stored ELF SHA-256 | Comparison |
|---|---:|---|---|
| verifier | 1507400 | `fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78` | MISMATCH current devnet and default; matches historical devnet config |
| pool | 605704 | `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` | MATCH current release and historical config |
| registry | 209280 | `7ad46f0d4b102a7c9699149d23bf6e065b6151feeaca95977d0a3146167d01ab` | MATCH historical devnet config (no separate current L188 ELF pin) |
| carrier | 20136 | `9d45bbcb0d68246993bd080f17f6ae116be48537e1a2c2bfd14602c590740ac2` | MATCH historical devnet config (no separate current L188 ELF pin) |

### Exact byte extraction and padding treatment

Decode base64 account data. Read little-endian u32 state tag at bytes 0–3,
u64 deployment slot at 4–11 and one-byte Option tag at 12. Tag 1 means the
32-byte authority is at 13–44; tag 0 means no authority. ProgramData ELF starts
at offset **45 even when authority is None**. Hashing includes no loader metadata.
The 45-byte fixed metadata size is also specified by locally installed
`solana-loader-v3-interface-7.0.0/src/state.rs::size_of_programdata_metadata`.

A loader allocation does not separately encode original ELF file length.
Determine the ELF64 little-endian file extent as the maximum of the ELF header
end, program-header table end, section-header table end, each segment's
`p_offset+p_filesz`, and each non-SHT_NOBITS section's `sh_offset+sh_size`.
Require the remaining allocation suffix to contain only zeros, and hash bytes
from ELF offset 0 to that extent. Extended section numbering is rejected by
this collector rather than guessed. This method retains zero bytes belonging
to the ELF, unlike an unconditional `rstrip(b'\0')`.

**For all four observed accounts the ELF extent equals the entire payload
length: zero allocation-padding bytes are removed.** Full payload SHA-256 equals
extracted ELF SHA-256 and the appropriate historical full-file pin in every case.
Each ELF legitimately ends in 15 zero bytes inside its final section-header
record; blindly stripping them gives incorrect hashes, recorded only as a
negative diagnostic in the JSON. No unrecorded ELF download or build was used.
These are stored loader input ELF hashes, not hashes of a relocated/JIT memory image.

## Validator version, feature accounts and runtime interpretation

getVersion reports `solana-core=4.4.0-beta.1`, `feature-set=3993424257`.
Every account context also reports `apiVersion=4.4.0-beta.1`.
This is the public RPC backend's self-report, not an attestation that every
validator runs identical binaries. The numeric feature-set value fingerprints
a software feature catalog; it is not an active-feature bitmap.
The finalized slot read was `516207225`; feature observations follow below.

Feature IDs were resolved from the locally installed `agave-feature-set-4.2.1`
source, whose SHA-256 and exact named module snippets are retained in the JSON.
This deliberately matches the source reference inspected in NDC. In particular,
the two V0 execution switches are **TestFeature placeholders in that source**;
their absent accounts do not independently authenticate which feature IDs or
rules the reported 4.4.0-beta.1 binary actually implements.

| Feature | Address | Observation | Activation slot | Read slot |
|---|---|---|---:|---:|
| `virtual_address_space_adjustments` | `7VgiehxNxu53KdxgLspGQY8myE6f7UokaWa4jsGcaSz` | active | 463536000 | 516207263 |
| `disable_sbpf_v0_execution` | `TestFeature11111111111111111111111111111111` | absent/inactive | — | 516207267 |
| `reenable_sbpf_v0_execution` | `TestFeature21111111111111111111111111111111` | absent/inactive | — | 516207271 |
| `enable_sbpf_v1_deployment_and_execution` | `JE86WkYvTrzW8HgNmrHY7dFYpCmSptUpKupbo2AdQ9cG` | active | 389664000 | 516207275 |
| `enable_sbpf_v2_deployment_and_execution` | `F6UVKh1ujTEFK3en2SyAL3cdVnqko1FVEXWhmdLRu6WP` | active | 396576000 | 516207279 |
| `enable_sbpf_v3_deployment_and_execution` | `5cC3foj77CWun58pC51ebHFUWavHWKarWyR5UUik7dnC` | active | 461808000 | 516207283 |
| `disable_sbpf_v0_v1_v2_deployment` | `B8JJXCy5amZyWG9r7EnUYLwzXSXTxG7GZ1qZ1qggo83g` | absent/inactive | — | 516207287 |

Existing feature accounts are owned by
`Feature111111111111111111111111111111111111`. Their nine-byte data consists of
Option tag 1 followed by a little-endian activation slot; each is earlier than
its finalized observation slot. A missing account is reported absent/inactive
for that exact queried address, not as a comprehensive feature-catalog audit.

All four observed ELFs have `e_flags=0`, hence SBPF V0 in the NDC-inspected
loader mapping. V1/V2/V3 activation does not rewrite a V0 ELF into a newer ABI.
Under the standard Agave feature-to-runtime mapping retained in
[NDC_STACK_FINDING.md](../native-sbfstack-20261028/NDC_STACK_FINDING.md),
active `virtual_address_space_adjustments` selects **no stack-frame gaps**
and disables the aligned mapping; V0 uses automatic fixed **4096-byte frames
and a 4096-byte call-frame bump**, default maximum call depth 64. Thus the
applicable *stock-runtime interpretation* is adjacent V0 frames, not the older
8192-byte bump with a 4096-byte unmapped gap. Whole-stack mapping is not
per-frame ownership enforcement: offsets beyond 4096 can reach another mapped
frame, so stack warnings are not generally fail-closed. A V0 execution-disable
rule, if implemented and active, would instead reject before execution.

**Retained runtime trust / limit:** the source inspected by NDC is Agave 4.2.1
and SBPF 0.21.1; the endpoint reports 4.4.0-beta.1. No 4.4 source, validator
executable hash, build flags, execution-budget settings, complete feature
catalog or cached executable was attested by the allowed RPC methods. These
reads establish the actual named feature-account state and ELF flags, and
select the above behavior *conditional on the validator preserving the
inspected stock mapping/defaults*. They do not close NDC's stronger exact
runtime-executable/source/build association. V0 is the version designated by
these programs' stored ELF; its execution admission is conditional on that
runtime trust, not demonstrated by a transaction in this task. No currently
executed SBF version or successful execution is inferred from `executable=true`.

NDC's warning-instance omission analysis concerns its three pinned release
ELFs. Because the deployed verifier hash differs, that omission result must
not be transferred to this historical deployed verifier without a separate
artifact analysis. Pool's matching bytes permit the identity association only;
all semantic/compiler/runtime conclusions retain NDC's stated scope.

## Exact manifest association statement

The following text can be incorporated into L188 without changing its target:

> NDQ observed finalized devnet state via https://api.devnet.solana.com on
> 2026-10-28 between 22:36:31.385008Z and 22:36:47.988489Z. For each program
> P listed above, its executable loader Program account (at its recorded
> Program read slot) links to ProgramData D. At D's finalized read slot S,
> SHA256(D.data[45:45+ELF_extent]) = H, deployment/last-upgrade slot = T,
> and upgrade authority = A, with P,D,S,H,T,A exactly as tabulated above.
> Pool's H equals the frozen release artifact hash
> 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
> The deployed verifier H is
> fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78,
> unequal to both current verifier pins; no current default-verifier deployment
> is associated. The RPC backend reports runtime V=4.4.0-beta.1 and catalog
> feature-set=3993424257. F is the seven exact feature-account observations
> and slots in NDQ_RPC_RECEIPTS.json, including active virtual_address_space_adjustments
> at activation slot 463536000. All observed ELFs designate V0. Adjacent
> 4096-byte V0 frames/no gaps follow under the explicitly retained stock
> feature/runtime mapping and budget/build trust, not an attested validator
> executable. L188 live current-verifier identity and exact runtime pin remain open.

The observations are a **vector of finalized slots**, not a single atomic
snapshot. getVersion has no context slot; do not invent one. ProgramData S is
an observation slot, distinct from stored deployment slot T. An authority can
upgrade Pool/carrier after the check, changing H, T or A. Verifier and registry
had no upgrade authority at their respective observations; ordinary loader
upgrade authority is therefore absent there. This is conditional on loader,
consensus and RPC integrity, not an unconditional forever guarantee. Feature
activation/runtime software and future cluster state can change independently.

Trust retained: public endpoint/TLS honesty and cluster selection; finalized
consensus/state reporting; loader state decoding and ELF extent interpretation;
SHA-256 collision resistance and receipt/local-tool integrity; validator
loader/runtime/ABI/budget/build semantics including the cross-version mapping;
compiler/library semantic preservation; theorem/source/model/refinement and
all other L188 trust boundaries. No cryptographic, Lean or Kani premise was
discharged, added or silently reclassified. Matching bytes establishes identity,
not acceptance behavior, source refinement, custody, availability, privacy or
100-bit campaign attack-work security.

The next release deliverable is an owner/lead decision and evidence associating
the **unchanged current pinned verifier** with an intended deployment, plus an
exact runtime source/executable/build/budget pin if the stronger NDC claim is
required. The mismatch is not permission to lower the target to historical
bytes. The read-only worker neither deploys nor recommends silently replacing
pins. No Lean, Kani, Rust build or manifest replay was run.
