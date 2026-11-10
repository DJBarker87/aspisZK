# PCXE_ HANDOFF: phase P6 refresh 2 (recount, combined import, trust-row naming)

Target not yet established. No ledger row, trust row, RSL, security contract or shipped source changed; no trust row added; nothing pushed or merged. Branch codex/pc-prov-p6t-20261110 (base research 74a3cf93287). Host workspace /home/dombarker/project-offloads/codex-pc-prov-p6t-20261110/.

Read PCXE_REPORT.md first, then PCXE_OWNER_DECISIONS.md. Machine-readable: PCXE_ALL_STATUS.json (merged status), PCXE_OVERLAY_LOG.json, PCXE_PROVENANCE.json, PCXE_ROW_TABLES.json, PCXE_DELTA.json, PCXE_AUDIT.json, PCXE_RENAMES.json, PCXE_CREDITED_FILES.json, PCXE_BUNDLES.json, PCXE_TRUST_NAMING.json (every DEPENDS_ON_LIBRARY_TRUST record and its row), PCXE_R22_SPLIT.json, PCXE_HAND_MODELS.json, PCXE_EXTERNALS.json, PCXE_TRUST_PROPOSALS.md, PCXE_NONFROZEN.json/.md, PCXE_NOSOURCE.json/.md, PCXE_L187_RECONCILE.json, PCXE_SHRAMT_UPGRADED.json, PCXE_NOT_ATTEMPTED_23.json, PCXE_SUPERSEDED.json, PCXE_STATUS_LINE.md, PCXE_CLASSIFICATIONS.json, PCXE_TOOLS.json, PCXE_ATTEMPTS.jsonl, receipts PCXE_Lnnn/receipt.json.

Ran: 8 of 14 Lean scopes, 0 extraction, 0 Kani, one at a time. Exit 0: L001 C18, L003 C19, L005 C20, L006 C21, L007 and L008 root. Exit 1 (bundler defects, replaced by a changed shape): L002 C19 (open namespace at end of a credited file), L004 C20 (duplicate root-level helper names across P3k files). Longest 60 s, peak RSS 6.3 GiB, swap 0, caps unraised; each admitted with host scopes below 6, Stream C below 2, disk above 40 GB. C01..C17 objects were reused by reference (P6c, P6x, P6r export directories; pinned by sha256 in the L008 receipt).

Re-run: bash PCXE_rerun.sh (local steps in order) after the host scopes, then bash PCXE_finalize.sh; run_scope.sh PCXE_L00n TARGET for a scope. Scratch inputs: the PCO partition tables in the session scratch directory (partE), row-relevant parts are inside PCXE_ROW_TABLES.json.

Not established: 466 OPEN cone definitions, 17 wrong-basis, 43 binding results, 7 trust-class records, 5 HAND_ADAPTED, 4 NO_FROZEN_COUNTERPART, 19 of 24 no-source modules, 22 of 26 non-frozen modules, 68 aspis-frozen externals, 23 array_from_fn dependants, release replay, L187/L188, R22, source-to-ELF.

Next deliverable: the binding-discharge round (Ext callee to gate item, deployed Ops satisfies Bound) and the extraction runs for the 263 definitions with no overflow-correct emission; owner decisions in PCXE_OWNER_DECISIONS.md part B.
