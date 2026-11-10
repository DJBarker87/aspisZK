#!/bin/bash
cd "$(dirname "$0")"
i=2
for m in AspisR1DotPushLocal_Funs AspisR1Post25Sampler_Funs CurrentClaimSumModel FinishCandidateExplicitOps NFS_AccumPart00 RPz7_AspisR1CircleSampleWrapper_Funs; do
  a=$(printf 'PCQL_L%03d' $i); bash run_scope.sh $a PRVEq_${m}_m1b; i=$((i+1))
done
