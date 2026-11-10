#!/bin/bash
# PCXF_chain2.sh: the L187-universe audit scopes after PCXF_L003 failed in the client pre-check (import Lean is not resolvable from the 9-entry chain; nothing was submitted to a scope; audit files no longer import Lean).
cd "$(dirname "$0")"
step() { a=$1; b=$2; shift 2
  env "$@" bash run_scope.sh $a $b
  echo "$a $b $(grep -E '"exit_status"|^exit=' $a.client.log | head -2 | cut -c1-120 | tr '\n' ' ')" >> chain1.log
  grep -q '"exit_status": 0' $a.client.log || { echo "STOP at $a $b" >> chain1.log; exit 1; }
}
step PCXF_L004 PCXF_AUD_L1 PCXF_LEAN_PATH_FILE=PCXF_LP_L1.json
step PCXF_L005 PCXF_AUD_L2A PCXF_LEAN_PATH_FILE=PCXF_LP_L2.json
step PCXF_L006 PCXF_AUD_L2B PCXF_LEAN_PATH_FILE=PCXF_LP_L2.json
step PCXF_L007 PCXF_AUD_L2C PCXF_LEAN_PATH_FILE=PCXF_LP_L2.json
echo done2 >> chain1.log
