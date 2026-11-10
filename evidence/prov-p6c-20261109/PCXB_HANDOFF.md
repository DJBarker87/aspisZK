# PCXB_ HANDOFF: phase P6 complete

Target not yet established. No ledger row, trust row, RSL, security contract or shipped source changed; nothing pushed or merged. Branch codex/pc-prov-p6c-20261109 (base research 54d05e1e61d); inputs from research 3ba71246350 (P3e) and evidence/shramt-20261110 (NPE_). Host workspace /home/dombarker/project-offloads/codex-pc-prov-p6c-20261109/.

Read PCXB_REPORT.md first, then PCXB_OWNER_DECISIONS.md. Machine-readable: PCXB_PROVENANCE.json (statuses per definition, per row), PCXB_AUDIT.json (scopes and axiom audit), PCXB_CREDITED_FILES.json, PCXB_BUNDLES.json, PCXB_SUPERSEDED.json, PCXB_R22_SPLIT.json, PCXB_HAND_MODELS.json, PCXB_EXTERNALS_601.json, PCXB_TRUST_PROPOSALS.md, PCXB_NONFROZEN.json/.md, PCXB_NOSOURCE.json/.md, PCXB_L187_RECONCILE.json, PCXB_L187_SWITCH.json, PCXB_SHRAMT_UPGRADED.json, PCXB_SECOND_TIER_OPEN.json, PCXB_STATUS_LINE.md, PCXB_CLASSIFICATIONS.json, PCXB_ATTEMPTS.jsonl, receipts PCXB_Lnnn/receipt.json.

Ran: 19 Lean scopes (L001 PRVH_WrapAdd; L002 failed audit-helper API; L003 helper ok; L004 failed wrapping shape; L005-L017 bundles C01-C13; L018 root v1; L019 root, final audit), 0 extraction, 0 Kani. Each admitted with host scopes < 6, Stream C < 2, disk >= 40 GB; caps unraised.

Re-run order: PCXB_credited.sh, PCXB_make_bundles.sh, run_scope.sh per target (PCXB_chain1.sh), PCXB_reach.sh, PCXB_compose1.sh, compose2, compose3, PCXB_nonfrozen_final.sh, PCXB_l187.sh, PCXB_nosource.sh, PCXB_hm3.sh, PCXB_trust.sh, PCXB_audit.sh, PCXB_final.sh. The scratch inputs (PCO partition tables) are the ones of the PCXA run, cloned from its scratch directory.

Next: remove the native.decide-bearing Debug-fmt declaration from the credited P4e fresh text or exclude it; owner decisions in PCXB_OWNER_DECISIONS.md.
