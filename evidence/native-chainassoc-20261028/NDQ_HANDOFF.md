# NDQ handoff

**MISMATCH: immutable deployed devnet verifier SHA-256 is
`fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78`,
not current devnet release `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
or default release `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`.
L188 obligation 5 remains open; target not yet established.**

Pool matches `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.
Registry and carrier match their historical public-config pins. Four deployed
programs were checked at finalized ProgramData slots 516207233, 516207243,
516207251 and 516207259. Verifier and registry have no upgrade authority;
Pool/carrier authority is `Xjb7roDVPDSPoZpUmDVUW5SMx21x7oQEg16dhb5TDXD`.
Full program IDs, linked ProgramData addresses, hashes, sizes and stored
last-upgrade slots are in [NDQ_CHAIN_ASSOCIATION.md](NDQ_CHAIN_ASSOCIATION.md).

The endpoint reports `4.4.0-beta.1`, catalog feature-set `3993424257`.
`virtual_address_space_adjustments` is active since slot 463536000.
All four stored ELFs designate SBPF V0 (`e_flags=0`). Under NDC's inspected
stock feature mapping this selects adjacent 4096-byte V0 frames with no gaps.
The mapping/budget/build interpretation remains trusted: NDC inspected Agave
4.2.1, whereas getVersion reports 4.4.0-beta.1. The two queried V0 execution
switch addresses are TestFeature placeholders in the 4.2.1 catalog; their
absence does not authenticate the newer validator's full catalog or admission
rules. No exact validator executable/source/build/budget attestation is supplied.

## Evidence and validation

- [NDQ_RPC_RECEIPTS.json](NDQ_RPC_RECEIPTS.json): all 17 requests with exact
  request/response SHA-256, UTC timestamps, decoded observations and 11 frozen
  repository-source pins. Raw request/response bytes are included alongside it.
- Read window: 2026-10-28T22:36:31.385008Z–22:36:47.988489Z;
  getVersion ×1, getSlot ×1, getAccountInfo ×15. No retry or scan.
- ProgramData header is always 45 bytes. ELF section/segment file extents
  establish that all four accounts have zero extra allocation padding.
  Each file's final 15 zero bytes belong to the ELF and must remain hashed.
- Fresh offline validation:
  `python3 -B evidence/native-chainassoc-20261028/NDQ_validate.py`, exit 0.
  Checked all raw hashes, request allowlist, loader links/owners/executable bits,
  authorities/slots, complete ELF payloads, feature-account decoding and source
  pins. `git diff --check` passed. No live query was repeated for validation.
- Reused release ledger, historical devnet config/report and NDC runtime analysis
  with explicit revision/hash pins; no artifact reproduction or semantic audit.

[NDQ_CHAIN_ASSOCIATION.md](NDQ_CHAIN_ASSOCIATION.md) contains exact text suitable
for the manifest. It associates each account hash with its own observation slot,
not an invented single snapshot. The manifest itself was not changed.
Pool/carrier remain upgradeable and can change after this check. RPC self-report
and finalized state remain endpoint/consensus trust, not executable attestation.
NDC's pinned-verifier warning-instance omission result cannot be transferred to
the different historical deployed verifier.

No mathematical/security premise was discharged, added or reclassified. This
packet establishes byte identity for Pool and the historical auxiliary artifacts,
and establishes a negative current-verifier association result. All compiler,
SDK/runtime, source/model/refinement, extraction, game and security obligations
remain in their documented scopes. No Lean, Kani, build, signing, wallet/key
access, airdrop, transaction or chain write occurred. No mainnet query occurred;
no mainnet deployment was identified in the inspected release sources.

## Remaining deliverable

The lead must retain the frozen current verifier target and decide how to obtain
its deployment association, then supply the exact runtime source/executable,
build-feature and execution-budget provenance required by L188 obligation 5.
The deployed verifier is immutable under ordinary loader rules; changing its
bytes is not an available upgrade of this identity. This read-only task does
not authorize a deployment, a replacement identity or a release-pin downgrade.

## Stages

1. `51aebc2874`: repository inventory and distinct release/historical pins.
2. `a863250191`: one bounded public RPC capture and frozen raw receipts.
3. This handoff commit: association finding, explicit runtime/time-of-check
   limitations and offline validation. No push.
