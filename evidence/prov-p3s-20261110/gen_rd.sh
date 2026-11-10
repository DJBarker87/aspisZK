#!/bin/bash
# generates PRVEq_Rd_<tag>.lean : frozen read_checkpoint_* (PCVU_E002) against the deployed reader ops (items 2 and 1 composed)
set -e
cd "$(dirname "$0")"
bash gen_rd_fresh.sh > /dev/null
OUT=${1:-PRVEq_Rd_s1.lean}
PROOF=${2:-PCVU_Rd_proof_s1.inc}
{
cat <<'EOF'
-- PCVU_ item (2): the frozen 4bb3b3f read_checkpoint_semantic_alpha / read_checkpoint_weights (emission PCVU_E002, overflow ON, text with the QM31::from_le_bytes
-- external and the Vec into_iter_mut external as parameters) against the deployed reader ops, stated as the Leaves sem/weights shape.
import Aeneas
import PRVEq_QM31_s3
import PRVEq_Tx2Deployed_s1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxRecDepth 2048
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
noncomputable section
namespace PCVU_Rd
open VTop_Stages VTop_Stages.PRVFresh_VTop_l1 AspisR1 PCVQ_Resumeq13
namespace PCVU_Fresh2
EOF
cat PCVU_Rd_fresh.inc
echo "end PCVU_Fresh2"
cat "$PROOF"
echo "end PCVU_Rd"
} > "$OUT"
