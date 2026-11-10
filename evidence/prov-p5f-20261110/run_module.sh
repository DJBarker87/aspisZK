# usage: bash run_module.sh MOD TAG FRESHDIR NS NEXTPROBE NEXTFINAL   (MOD like RPu_FIq_Native07, TAG n07)
cd "$(dirname "$0")"
M=$1;T=$2;F=$3;NS=$4;LP=$5;LF=$6
L=$(python3 mk_only.py $M inputs/only_$T.json | cut -d' ' -f2-); echo $L > gen/$T.loops
python3 -B PCWP_pipeline.py probe $M $T $F $NS inputs/only_$T.json | tail -1
bash run_scope.sh $LP PRVEq_${M}_$T | head -1 | cut -c1-90
xz -dc $LP/stdout.log.xz > gen/${T}_$LP.log; echo "probe errors: $(grep -c error gen/${T}_$LP.log)"
python3 -B PCWP_pipeline.py final $M $T $F $NS inputs/only_$T.json $L LOG=gen/${T}_$LP.log | tail -1
bash run_scope.sh $LF PRVEq_${M}_${T}_c | head -1 | cut -c1-90
xz -dc $LF/stdout.log.xz > gen/${T}_$LF.log; echo "final errors: $(grep -c error gen/${T}_$LF.log) ERRTOK_AX: $(grep -c ERRTOK_AX gen/${T}_$LF.log)"; tail -1 $LF.client.log
rm -rf __pycache__
