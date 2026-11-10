#!/bin/bash
# usage: bash PCQK_fetch.sh MODULE_Funs_path  -> copies research:<path> and its sibling Types.lean into inputs/ (gate_<M>.lean, gatetypes_<M>.lean)
cd "$(dirname "$0")"; R=/Users/dominic/ZK
p=$1; m=$2
git -C $R show research:$p > inputs/gate_${m//./_}.lean
t=$(dirname $p)/Types.lean
git -C $R show research:$t > inputs/gatetypes_${m//./_}.lean 2>/dev/null || rm -f inputs/gatetypes_${m//./_}.lean
ls -la inputs | grep ${m//./_}
