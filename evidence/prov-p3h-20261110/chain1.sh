cd "$(dirname "$0")"
i=9
for t in AspisR1QueryGeometryActual_Funs_n1 AspisR1EbyKFinish_Funs_n1 CurrentCompactCallerModelV1_n1 CurrentCompactCallerModelV1_n2 FinishCandidateExplicitOps_n1 VTop_Model_n1 AspisR1PublicPreparation_Types_n1 AspisR1PublicPreparation_Types_n2 Stage2ContinuationTypes_n1 Stage2ContinuationTypes_n2 RPz7_FIo_NativeTypes_n1; do
  id=$(printf 'PCVH_L%03d' $i); i=$((i+1))
  timeout 1500 python3 -B PCVH_run.py $id lean PRVEq_$t > $id.out 2>&1
  echo "$id $t exit=$?" >> chain1.log
done
echo ALLDONE >> chain1.log
