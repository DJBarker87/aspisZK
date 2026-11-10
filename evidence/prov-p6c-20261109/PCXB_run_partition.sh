#!/bin/bash
# Re-run the PCO partition pipeline (read-only on git objects) at the PCO base revision to get the emitted-module declaration tables.
set -e
SCR=/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/partc
cd /Users/dominic/ZK/.worktrees/pc-prov-p6c/evidence
python3 -I prov-p0-20261109/PCO_partition.py --rev 6ce07a6a593 --gate-dir ledger30-20261111 --gate-prefix NNN --scratch $SCR --out $SCR/partc.json --stages tree,ledger,scan,modmap,hits,classify,final > $SCR.log 2>&1
echo done >> $SCR.log
