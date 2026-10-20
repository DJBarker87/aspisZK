# Frozen R1 / Pool encoding uniqueness — 2026-10-21

Status: source inventory in progress; focused native evidence pending.

Scope: branch `codex/cx-encoding-inj-20261021`, base `3657df3e0`.
No shipped implementation changes. The question is injectivity of accepted
wire encodings into the complete logical statement, including raw account
addresses and transcript bindings, not of the semantic field projection alone.

Frozen ELF identities (SHA-256, not git commits):

- default verifier: `dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34`
- devnet verifier: `fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78`
- Pool: `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

Source-to-pin evidence is the existing
`docs/research/100bit-spend-path-20261013/evidence/asq8-kani-20261021/relocation-elf-identities.json`
and corresponding relocation build receipts. This job adds native tests and
source hashes, not another SBF rebuild.

## Inventory

To be completed with decoder paths, per-field behavior and evidence.

## Native evidence

Focused harness: `tools/encoding-uniqueness/`. No keys or live accounts are used.

## Formal interpretation and proposed changes

Pending completion of source tracing and tests.
