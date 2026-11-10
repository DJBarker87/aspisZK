#!/bin/bash
# PCXG_chain_root.sh: after the all-in-one root PRVCmb_L187_ROOT failed at import (PCVH.dec_qm declared in PRVCmb_C19 and in PRVEq_PCVH_R1CandidateWideParserSource_k1; PCXG_L019), the bundles-only root and the separate audit modules.
cd "$(dirname "$0")"
step() { a=$1; shift
  bash run_scope.sh $a "$1"
  echo "$a $1 $(grep -E '^exit=' $a.client.log | tail -1)" >> PCXG_chain3.log
  grep -q '^exit=0' $a.client.log || { echo "STOP at $a" >> PCXG_chain3.log; exit 1; }
}
step PCXG_L020 PRVCmb_L187_ROOTB
step PCXG_L021 PCXG_AUD_L1,PCXG_AUD_L2A,PCXG_AUD_L2B,PCXG_AUD_L2C
echo done >> PCXG_chain3.log
