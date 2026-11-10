# PCXG_ HANDOFF: phase P6 replay of every credited provenance file in the L187 closure (in progress)

Target not yet established. No ledger row, trust row, RSL, security contract or shipped source changed; nothing pushed or merged.
Branch codex/pc-prov-p6v-20261110 (base research f7a1c429f39). Host workspace /home/dombarker/project-offloads/codex-pc-prov-p6v-20261110/.

Method: the 22 PCXF bundles (PRVCmb_C01..C22, 293 credited files, sources copied unchanged from the PCXB/PCXC/PCXD/PCXE/PCXF directories; C13 from PCXC) plus PRVH_WrapAdd and
the 28 deployed-body modules (chains PCVN/PCVQ/PCVS tx2, PCVP NOC stage1/stage2/prepare/tx1, sources from prov-p3h/l/n/o/p/q/r) are recompiled with plain `lean` (no lake env)
and LEAN_PATH = own PCXG_exports, L187 final/objs, L187 objs, L187 base_ref. Several modules are compiled one after another inside one capped scope (6G/8G, swap 0, 180 s per Lean process).
Re-run: bash PCXG_chain_bundles.sh, then bash PCXG_chain_deployed.sh, then the root scope (run_scope.sh PCXG_Lnnn PRVCmb_L187_ROOT), then bash PCXG_audit.sh.
Read PCXG_REPORT.md when it exists; PCXG_ATTEMPTS.jsonl and PCXG_Lnnn/receipt.json hold every scope.
