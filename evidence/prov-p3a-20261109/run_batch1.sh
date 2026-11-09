#!/bin/bash
# generate P3 variants (undrop + obligations) and compile each in its own scope, serially
cd "$(dirname "$0")"
n=${START:-5}
for m in AdapterRwModel OraclePortCkptAbi2Extracted_Funs AspisR1CircleFallback_Funs RPu_FIq_Native08 NHJ_SnapshotReference_Funs NDE_Reference2_Funs NDE_Reference5_Funs NJC_ValidateEmission NNG_verify_finish_Funs NMP_prepare_Funs; do
  python3 PCVA_p3gen.py ../prov-p5-20261109/PRVEq_$m.lean ../prov-p5-20261109/inputs/fresh_$m/Funs.lean PRVEq_${m}_P3.lean
  id=$(printf "PCVA_L%03d" $n); n=$((n+1))
  python3 PCVA_run.py $id lean PRVEq_${m}_P3 > run_$id.out 2>&1
  xz -dc $id/stdout.log.xz > $id/log.txt
  echo "$m $id exit=$(python3 -c "import json;print(json.load(open('$id/receipt.json'))['exit_status'])") errors=$(grep -c 'error' $id/log.txt)"
done
