# Legacy Pool instruction removal — record (2026-11-09)

Owner decision, 2026-11-09: "delete them but keep a record in case we find something breaks without them later."

## What is removed from the release Pool (programs/aspis-pool)

Frozen source before removal: revision 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387, Pool ELF 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
Restore any of it with `git show 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:<path>`.

| Magic | Instruction | Frozen root (file:line at 4bb3b3f) | Role |
|---|---|---|---|
| ASIN | legacy initialize | processor.rs::process_initialize_with_runtime_v1:625 | creates legacy single-tree Pool accounts |
| ASDI | legacy vault-backed deposit | processor.rs::process_deposit_with_runtime_v1:738 | deposit into the legacy tree |
| ASPT | legacy private transfer | processor.rs::process_private_transfer_with_runtime_v1:2024 | verifier-gated transfer on the legacy tree |
| ASWD | legacy withdrawal | processor.rs::process_withdrawal_with_runtime_v1:2189 | verifier-gated withdrawal on the legacy tree |
| ASPP | prepare settlement | processor.rs::process_prepare_settlement_with_runtime_v1:1167 | first half of the split (prepared) settlement: Merkle/Poseidon work |
| ASPF | settle prepared | processor.rs::process_settle_prepared_with_runtime_v1:1674 | final gate of the prepared settlement |
| ASPX | cancel prepared settlement | processor.rs::process_cancel_prepared_settlement_with_runtime_v1:1484 | refund/close a prepared plan |

Supporting modules expected to become unused: prepared_settlement.rs, prepared_settlement_format.rs, prepared_settlement_instruction.rs, settle_prepared_instruction.rs, cancel_prepared_settlement_instruction.rs, and the legacy-only parts of processor.rs, instruction.rs, deposit.rs, deposit_transport.rs, state.rs, vault.rs. The exact deleted list is in the implementation job's receipts (evidence/legacy-removal-20261109).

## What stays

The pair-forest path: AS8I (pair-forest initialize), AS8C (checkpoint), AS8D (deposit), ASQ8 (verifier-gated terminal: transfer/withdrawal), plus the cfg-disabled ASF8/ASJP/ASJW exactly as before. Every function reached from those roots must keep a byte-identical body (frozen body sha256 as in evidence/pool-inventory-20261109/NKS_INVENTORY.json).

## Why

Nothing in the R1 spend path (pair-forest + r1-cost-probe verifier) calls the legacy instructions or prepared settlement (checked: pair_forest*.rs and pair_processor.rs reference none of them). They were in scope only because the deployed Pool compiled them, so an attacker could call them. Removing them drops about 210 of the 494 new Pool rows and about 5 of the 13 exclusive-guard owners (NKS_ inventory, lead split), and removes an unused attack surface.

## Effect on proofs

crates/ and programs/r1-cost-probe are unchanged, so every ledger row, native receipt, frozen body hash and the verifier ELF pins (default f8c0ec72…, devnet 63ad3e9c…) stand. Existing Pool support (NIB_ read_to_settlement, guard/CPI support) targets the pair-forest path and stands if the body hashes are unchanged. The Pool ELF pin changes; the Pool inventory is regenerated on the new revision.

## If something breaks later

Symptoms to watch: a client or test sending ASIN/ASDI/ASPT/ASWD/ASPP/ASPF/ASPX now gets an invalid-instruction error; any flow that relied on splitting settlement across transactions for compute. To restore, re-add the files/functions from 4bb3b3f; that re-expands the Pool proof scope by the rows listed in NKS_INVENTORY.json for those roots.
