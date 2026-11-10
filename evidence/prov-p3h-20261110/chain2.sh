cd "$(dirname "$0")"
i=20
for t in AspisR1QueryGeometryActual_Funs_m1 Stage2ContinuationTypes_n1 Stage2ContinuationTypes_n2; do
  id=$(printf 'PCVH_L%03d' $i); i=$((i+1))
  timeout 1500 python3 -B PCVH_run.py $id lean PRVEq_$t > $id.out 2>&1
  echo "$id $t exit=$?" >> chain2.log
done
echo ALLDONE >> chain2.log
