# PCXD_ HANDOFF: phase P6 refresh (final recount and combined import)

Target not yet established. No ledger row, trust row, RSL, security contract or shipped source changed; nothing pushed or merged. Branch codex/pc-prov-p6r-20261110 (base research c933144b87e). Host workspace /home/dombarker/project-offloads/codex-pc-prov-p6r-20261110/.

Read PCXD_REPORT.md first, then PCXD_OWNER_DECISIONS.md. Machine-readable: PCXD_PROVENANCE.json, PCXD_ROW_TABLES.json (new: row-to-module and row-to-definition tables, 15.5 MB, method in PCXD_rowtables.sh), PCXD_DELTA.json, PCXD_AUDIT.json, PCXD_RENAMES.json, PCXD_CREDITED_FILES.json, PCXD_BUNDLES.json, PCXD_SUPERSEDED.json, PCXD_R22_SPLIT.json, PCXD_HAND_MODELS.json, PCXD_EXTERNALS.json, PCXD_TRUST_PROPOSALS.md, PCXD_NONFROZEN.json/.md, PCXD_NOSOURCE.json/.md, PCXD_L187_RECONCILE.json, PCXD_SHRAMT_UPGRADED.json, PCXD_NOT_ATTEMPTED_23.json, PCXD_STATUS_LINE.md, PCXD_CLASSIFICATIONS.json, PCXD_TOOLS.json, PCXD_ATTEMPTS.jsonl, receipts PCXD_Lnnn/receipt.json.

Ran: 5 of 14 Lean scopes (L001 C14, L002 C15, L003 C16, L004 C17, L005 ROOT), all exit 0, 0 extraction, 0 Kani. Longest 39 s, peak RSS 6.2 GiB (root), swap 0. Each admitted with host scopes < 6, Stream C < 2, disk >= 40 GB; caps unraised. C01..C13 objects were reused (pinned by sha256 in the PCXD_L005 receipt).

Re-run order: PCXD_TOOLS.json rerun_order. The scratch inputs (PCO partition tables) are those of the PCXA/PCXB run; the row-relevant parts are now inside PCXD_ROW_TABLES.json.

Not established: the 554 OPEN cone definitions (325 need an overflow-correct fresh emission, which is extraction work), the 23 records P2j did not attempt, 33 HAND_ADAPTED, 4 NO_FROZEN_COUNTERPART, 20 of 24 no-source modules, at most 99 externals, and everything outside provenance (release replay, L187/L188, R22, source-to-ELF).

Next deliverable: owner decisions in PCXD_OWNER_DECISIONS.md (no-source modules R/F, trust classes, the 8 reached gate-only definitions, the nine-closure ruling); then extraction runs for the 325 definitions with no overflow-correct emission.
