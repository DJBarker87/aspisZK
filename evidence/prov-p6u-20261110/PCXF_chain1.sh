#!/bin/bash
# PCXF_chain1.sh: the host scopes, strictly one at a time (stops at the first non-zero exit).
cd "$(dirname "$0")"
step() { a=$1; b=$2; shift 2
  env "$@" bash run_scope.sh $a $b
  echo "$a $b $(grep -E '"exit_status"|^exit=' $a.client.log | head -2 | tr '\n' ' ')" >> chain1.log
  grep -q '"exit_status": 0' $a.client.log || { echo "STOP at $a $b" >> chain1.log; exit 1; }
}
step PCXF_L001 PRVCmb_C22 X=1
step PCXF_L002 PRVCmb_ROOT X=1
step PCXF_L003 PCXF_AUD_L1 PCXF_LEAN_PATH_FILE=PCXF_LP_L1.json
step PCXF_L004 PCXF_AUD_L2A PCXF_LEAN_PATH_FILE=PCXF_LP_L2.json
step PCXF_L005 PCXF_AUD_L2B PCXF_LEAN_PATH_FILE=PCXF_LP_L2.json
step PCXF_L006 PCXF_AUD_L2C PCXF_LEAN_PATH_FILE=PCXF_LP_L2.json
echo done >> chain1.log
