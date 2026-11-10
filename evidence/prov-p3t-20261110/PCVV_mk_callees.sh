#!/bin/bash
# usage: bash PCVV_mk_callees.sh OUT.lean [EXTRA_LEAN_FILE]  -- assemble the fresh callee text (Ext fragment) in namespace AdapterRw.PCVV_S3
cd "$(dirname "$0")"
R=PCVV_E008_ext_fragment.lean
{
echo "-- PCVV_ AdapterRw callees: fresh text from PCVV_E008 (original Aeneas 959659a6, overflow ON, frozen 4bb3b3f, LLBC PCVV_E006), externals as fields of Ext."
cat <<'H'
import Aeneas
import AdapterRwModel
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AdapterRw
namespace PCVV_S3
H
grep -E "^def r1_pool_adapter\.(decode_public_statement_box|decode_master_box|decode_checkpoint_box|scan_proof_buffer)\.closure(_1)? := Unit" PCVV_E008_Types.lean
cat $R
if [ -n "$2" ]; then cat "$2"; fi
echo "end PCVV_S3"
echo "end AdapterRw"
} > "$1"
