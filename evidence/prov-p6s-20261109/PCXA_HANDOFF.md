# PCXA_ HANDOFF: phase P6 snapshot (composition audit, provenance status, hand-model inventory)

Target not yet established. No ledger row, trust row, RSL, security contract or shipped source changed; nothing pushed or merged. Branch codex/pc-prov-p6s-20261109 (base research 65f42e74c0d). Host workspace /home/dombarker/project-offloads/codex-pc-prov-p6s-20261109/. This is the first of two P6 runs; the OPEN remainder is large (see PCXA_REPORT.md).

## What ran
12 Lean scopes (PCXA_L001-L012), 0 extraction, 0 Kani, one at a time, caps 6G/8G, swap 0, 180 s unraised. Admission per launch: host scopes < 6, Stream C < 2, disk >= 40 GB (PCXA_Lnnn-admission.json, -disk-*.json). 11 exit 0; L006 (bundle A6) exit 1, shape retired and replaced by L011 + L012 (PCXA-C2). Longest wall 97.5 s (L011), peak RSS 6.0 GiB (L010). Receipts PCXA_Lnnn/receipt.json, PCXA_ATTEMPTS.jsonl. Everything else is local computation over git objects (scripts PCXA_*.sh, PCXA_lib.py; scratch outside the repo: re-run PCXA_run_partition.sh first).

## Files
PCXA_AUDIT.json, PCXA_PROVENANCE.json (4.9 MB), PCXA_R22_SPLIT.json, PCXA_HAND_MODELS.json, PCXA_TRUST_PROPOSALS.md, PCXA_NOSOURCE.json/.md, PCXA_L187_RECONCILE.json, PCXA_NONFROZEN.json/.md (+ PCXA_NONFROZEN_DETECT.json, first detector pass), PCXA_STATUS_LINE.md, PCXA_REPORT.md, PCXA_CLASSIFICATIONS.json, PCXA_BUNDLES*.json, PRVEq_bundle_A*.lean (compile vehicles), PCXA_SPLITB_HITS.json.

## Order of re-run
PCXA_run_partition.sh, PCXA_reach.sh, PCXA_compose1.sh, PCXA_compose2.sh, PCXA_compose3.sh, PCXA_nonfrozen2.sh, PCXA_nonfrozen3.sh, PCXA_l187.sh (needs L187_SOURCE_FIXES.jsonl in the scratch input dir), PCXA_nosource.sh, PCXA_hm1.sh, PCXA_hm2.sh, PCXA_trust.sh, PCXA_audit.sh, PCXA_final.sh. P4b/P4c inputs are read with git show (sparse list unchanged).

## Next
The second P6 run should take the P1f emissions and the P3 M31.mul result, and recompute from PCUF_ALL_STATUS successors. The ledger job consumes PCXA_PROVENANCE.json and PCXA_STATUS_LINE.md.
