# CB9 direct extraction handoff

Branch: codex/pv-cb9-20261027. Base: a436dadfee.

Rows discharged: **0**. Four independent OPEN rows were requested; nine named candidates were inspected, op259 was SKIP(sibling), eight had direct shipped roots extracted to LLBC with the pinned Charon; op252 also has a current-crate path-module coverage correction (OP252-COVERAGE.md). Read ROWS.md for per-op status and INVENTORY.md for exact pinned Aeneas refusals.

No theorem added; no `opN_source` law is claimed for these roots. `#print axioms`: N/A for extraction processes. No Lean compilation was launched because no root reached a nonempty generated Lean extraction. The existing PV_CB3_CallbackBundle and all ProverRw* files are unchanged. No privacy endpoint premise was removed, added or changed. No counterexample was found. The privacy target is **not yet established**.

## Validation receipts

Every target and complete revision is retained in RECEIPTS.json and the per-run receipt.json. All scopes used MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; one scope at a time. Compilation/extraction was optimized release. The pinned binary SHA-256 values match retained-extractor-pins.txt from the base cb3 evidence (Aeneas 562e1f51..., Charon daad69be...). No preflight switch was disabled.

| op | phase | exit | wall | peak RSS KiB | swaps | revision |
|---|---|---|---|---|---|---|
| op226 | Aeneas | 2 | 0:00.54 | 57552 | 0 | `ff2bc6d0dd` |
| op226 | Charon | 0 | 0:05.29 | 275544 | 0 | `ff2bc6d0dd` |
| op227 | Aeneas | 2 | 0:00.53 | 78672 | 0 | `c356f8a214` |
| op227 | Charon | 0 | 0:05.13 | 296380 | 0 | `c356f8a214` |
| op228 | Aeneas | 2 | 0:00.23 | 53152 | 0 | `c356f8a214` |
| op228 | Charon | 0 | 0:05.65 | 277796 | 0 | `c356f8a214` |
| op230 | Aeneas | 2 | 0:00.17 | 47520 | 0 | `924b1badba` |
| op230 | Charon | 0 | 0:09.45 | 272608 | 0 | `924b1badba` |
| op250 | Aeneas | 2 | 0:00.26 | 49808 | 0 | `924b1badba` |
| op250 | Charon | 0 | 0:06.23 | 279372 | 0 | `924b1badba` |
| op251 | Aeneas | 2 | 0:00.29 | 52624 | 0 | `14638e4e76` |
| op251 | Charon | 0 | 0:05.41 | 276960 | 0 | `14638e4e76` |
| op252 | Aeneas | 0 | 0:00.58 | 58784 | 0 | `14638e4e76` |
| op252 | Charon | 0 | 0:06.83 | 273600 | 0 | `14638e4e76` |
| op252current | Aeneas | 2 | 0:00.21 | 51392 | 0 | `14638e4e76` |
| op252current | Charon | 0 | 0:06.79 | 280088 | 0 | `14638e4e76` |
| op254 | Aeneas | 2 | 0:00.31 | 48224 | 0 | `a436dadfee` |
| op254 | Charon | 0 | 1:17.72 | 577348 | 0 | `a436dadfee` |

786 host snapshot files match tracked worktree bytes (source-identity.json). LLBC-AUDIT.json verifies actual root names, source spans, structured bodies and has_errors=false. These checks establish extraction input coverage, not a source-to-model theorem. The mutable historical LLBCs were not reused or attributed to historical evidence: this run uses unique PV_CB3_CB9OpN files.

## Budget and boundaries

Lean: 0/100. Kani: 0/4. Env-J IDs: none used, next 51500. 51797–51799 remain reserved for the bundle audit. No shared env-J source written. No shipped source changed. No keys touched. No Kani field arithmetic runs. Native-effect obligations are recorded separately in NATIVE-DEFERRALS.md for pv-runjoin.

The instruction to move on after each refusal prevents an unchanged retry or an unapproved reference workaround. The budget is unspent, not exhausted. A lead decision is requested for additional eligible direct-extraction rows or route (ii); no source-law or audit compile will be fabricated to consume the budget.

Next concrete deliverable: lead-selected additional extraction rows or a lead-approved route (ii) with its shipped-source link; then complete Result source equations for four rows, additive PV_CB3_CallbackBundle composition, and the reserved bundle audit.

## Commits from the requested base

```text
14638e4e76 Record helper sum and ordinary sampler extraction refusals
924b1badba Record terminal and registry extraction preflight obstructions
c356f8a214 Record direct shipped extraction refusals for public bytes and powers
ff2bc6d0dd Record callback recount and direct extraction preflight
```
