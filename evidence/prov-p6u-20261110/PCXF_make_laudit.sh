#!/bin/bash
# PCXF_make_laudit.sh: audit modules for the credited deployed-top-body results that compile only in the L187-closure universe (PCXF-C3).
# Each audit file imports the credited modules BY REFERENCE (objects from the PCVN/PCVQ/PCVS/PCVP exports; not renamed bundles, because the files import one another and the base modules clash) and audits every theorem whose name contains the job tag.
cd "$(dirname "$0")"
DEF=PCXF_audit_def.lean.in
mk() { # name label infixes imports...
  local name=$1 label=$2 infix=$3; shift 3
  { echo "-- PCXF audit module $name ($label): imports the credited modules by reference, then one audit pass over every constant whose name contains one of: $infix"
    echo "import Aeneas"; echo "import Lean"
    for m in "$@"; do echo "import $m"; done
    cat $DEF
    local pred="fun n => let s := n.toString; [$infix].any (fun k => (s.splitOn k).length > 1)"
    echo "#eval PRVCmbAudit.auditRoot \"$label\" ($pred)"
  } > $name.lean
}
mk PCXF_AUD_L1 "tx2 chain PCVN/PCVQ/PCVS" '"PCVN_", "PCVQ_", "PCVS_"' PRVEq_Tx2Deployed_n0 PRVEq_Op2_p5 PRVEq_Op13_p1 PRVEq_Op17_p2 PRVEq_Tx2Deployed_n1 PRVEq_Resume_q13 PRVEq_Tx2Deployed_q5 PRVEq_Validate_q2 PRVEq_Tx2Deployed_q6 PRVEq_DeriveRef_q1 PRVEq_E32_s4 PRVEq_Tx2Deployed_s1 PRVEq_WideBind_s2 PRVEq_Op17_s2 PRVEq_CkptSmall_s4 PRVEq_Tx2Deployed_s2
mk PCXF_AUD_L2A "stage1 NOC PCVP" '"PCVP_"' PRVEq_AdapterStage1DeployedNOC_o1 PRVEq_NocStage1Compose_o1
mk PCXF_AUD_L2B "stage2 NOC PCVP" '"PCVP_"' PRVEq_AdapterStage2DeployedNOC_o1
mk PCXF_AUD_L2C "prepare/tx1 NOC PCVP" '"PCVP_"' PRVEq_CallerPrepTx1DeployedNOC_o1 PRVEq_NocPrepTx1Compose_o1 PRVEq_NocCallerSlots_o1 PRVEq_NocCallerSlots2_o1
ls -la PCXF_AUD_L*.lean
