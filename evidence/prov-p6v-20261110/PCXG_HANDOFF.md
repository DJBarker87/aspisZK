# PCXG_ HANDOFF: phase P6 replay of every credited provenance file in the L187 closure (complete)

Target not yet established. No ledger row, trust row, RSL, security contract or shipped source changed; nothing pushed or merged.
Branch codex/pc-prov-p6v-20261110 (base research f7a1c429f39). Host workspace /home/dombarker/project-offloads/codex-pc-prov-p6v-20261110/.

Method: the 22 PCXF bundles (PRVCmb_C01..C22, 293 credited files, sources copied unchanged from the PCXB/PCXC/PCXD/PCXE/PCXF directories; C13 from PCXC) plus PRVH_WrapAdd and
the 28 deployed-body modules (chains PCVN/PCVQ/PCVS tx2, PCVP NOC stage1/stage2/prepare/tx1, sources from prov-p3h/l/n/o/p/q/r) are recompiled with plain `lean` (no lake env)
and LEAN_PATH = own PCXG_exports, L187 final/objs, L187 objs, L187 base_ref. Several modules are compiled one after another inside one capped scope (6G/8G, swap 0, 180 s per Lean process).
Re-run: bash PCXG_chain_bundles.sh, then bash PCXG_chain_deployed.sh, then the root scope (run_scope.sh PCXG_Lnnn PRVCmb_L187_ROOT), then bash PCXG_audit.sh.
Read PCXG_REPORT.md first (result: all credited files hold against L187; settled 993, not settled 649, other classes 65; two shape changes F1, F2); PCXG_ATTEMPTS.jsonl and PCXG_Lnnn/receipt.json hold every scope.

Machine-readable: PCXG_AUDIT.json (root PRVCmb_L187_ROOTB), PCXG_AUDIT_L.json (deployed names), PCXG_UNIVERSE_FINDINGS.json, PCXG_IMPORT_VERSIONS.json, PCXG_ROWS_ON_LEDGER30_VERSIONS.json, PCXG_PROVENANCE.json, PCXG_ROW_TABLES.json, PCXG_DELTA.json, PCXG_CLASSIFICATIONS.json, PCXG_TOOLS.json, PCXG_ATTEMPTS.jsonl, PCXG_Lnnn/receipt.json (21 scopes; L012 timeout and L019 import clash are the two non-zero).
Not established: see PCXG_REPORT.md section 6. Next deliverables: single-import-friendly combined root (needs the clashing PCVH.dec_qm and the three PRVEq base modules renamed by the rename tool, a source-text change that needs the lead's say), the 649 not-settled definitions, pin-equal evidence for the 183 receipted definitions.
Remote: nothing running; host workspace holds 180 MB (own exports and logs).
