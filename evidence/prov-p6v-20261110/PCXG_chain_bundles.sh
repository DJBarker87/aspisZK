#!/bin/bash
# PCXG_chain_bundles.sh: the bundle scopes strictly one at a time (continues past a failed scope, because bundles are independent; failures are listed in PCXG_chain.log).
cd "$(dirname "$0")"
step() { a=$1; shift
  bash run_scope.sh $a "$1"
  echo "$a $1 $(grep -E '^exit=' $a.client.log | tail -1)" >> PCXG_chain.log
}
step PCXG_L002 PRVCmb_C02
step PCXG_L003 PRVCmb_C05
step PCXG_L004 PRVCmb_C06,PRVCmb_C14
step PCXG_L005 PRVCmb_C07
step PCXG_L006 PRVCmb_C08
step PCXG_L007 PRVCmb_C09
step PCXG_L008 PRVCmb_C10,PRVCmb_C15
step PCXG_L009 PRVCmb_C11
step PCXG_L010 PRVCmb_C12
step PCXG_L011 PRVCmb_C13
step PCXG_L012 PRVCmb_C16,PRVCmb_C18
step PCXG_L013 PRVCmb_C19,PRVCmb_C20,PRVCmb_C21
echo done >> PCXG_chain.log
