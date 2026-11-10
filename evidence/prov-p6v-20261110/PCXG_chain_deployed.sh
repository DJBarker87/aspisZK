#!/bin/bash
# PCXG_chain_deployed.sh (second version: C18 split into C18A..D after the L012 timeout of C18 at 180 s): waits for PCXG_chain.log 'done', then the deployed-module scopes one at a time; stops at the first failed scope (the modules depend on each other).
cd "$(dirname "$0")"
until grep -q '^done' PCXG_chain.log 2>/dev/null; do sleep 30; done
step() { a=$1; shift
  bash run_scope.sh $a "$1"
  echo "$a $1 $(grep -E '^exit=' $a.client.log | tail -1)" >> PCXG_chain2.log
  grep -q '^exit=0' $a.client.log || { echo "STOP at $a" >> PCXG_chain2.log; exit 1; }
}
step PCXG_L014 PRVCmb_C18A,PRVCmb_C18B
step PCXG_L015 PRVCmb_C18C,PRVCmb_C18D
step PCXG_L016 PRVEq_VTop_l1,PRVEq_Tx2Deployed_n0,PRVEq_PCVH_R1CandidateWideParserSource_k1,PRVEq_Op2_p5,PRVEq_Op13_p1,PRVEq_Op17_p2,PRVEq_Tx2Deployed_n1,PRVEq_Resume_q13,PRVEq_Tx2Deployed_q5,PRVEq_Validate_q2,PRVEq_Tx2Deployed_q6,PRVEq_DeriveRef_q1
step PCXG_L017 PRVEq_E32_s4,PRVEq_Tx2Deployed_s1,PRVEq_WideBind_s2,PRVEq_Op17_s2,PRVEq_CkptSmall_s4,PRVEq_Tx2Deployed_s2
step PCXG_L018 PRVEq_AdapterStage1_o1,PRVEq_AdapterStage1DeployedNOC_o1,PRVEq_NocStage1Compose_o1,PRVEq_AdapterStage2_o1,PRVEq_AdapterStage2DeployedNOC_o1,PRVEq_CallerPrepTx1_o1,PRVEq_CallerPrepTx1DeployedNOC_o1,PRVEq_NocPrepTx1Compose_o1,PRVEq_NocCallerSlots_o1,PRVEq_NocCallerSlots2_o1
echo done >> PCXG_chain2.log
