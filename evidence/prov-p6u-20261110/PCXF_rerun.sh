#!/bin/bash
# PCXF_rerun.sh: the local (non-host) steps in order. Host Lean scopes (bundles C18..C21 and ROOT) run by run_scope.sh / PCXF_chain1.sh before PCXF_audit.sh.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6u
(cd evidence && python3 -I -B prov-p6u-20261110/PCXF_overlay.py) > /tmp/pcxe_overlay.out 2>&1 || exit 1
for s in credited make_bundles; do bash evidence/prov-p6u-20261110/PCXF_$s.sh > /tmp/pcxe_$s.out 2>&1 || exit 1; done
for s in reach compose1 compose2 compose3 nonfrozen_final l187 nosource shramt hm3 externals trust audit final delta notattempted rowtables; do bash evidence/prov-p6u-20261110/PCXF_$s.sh > /tmp/pcxe_$s.out 2>&1 || { echo "FAIL $s"; exit 1; }; done
echo ok
