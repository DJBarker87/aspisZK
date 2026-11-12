#!/bin/bash
# X1 stage 2: inside ONE fv_slot.sh scope, the lead\x27s SBF build (fv_frz_build.sh) of the unmodified copy and of the rewrite tree.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
P=37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt; R=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q
for t in "$@"; do n=${t%%=*}; tree=${t#*=}; bash $W/fv_frz_build.sh $n $tree aspis $P $R > $W/x1/logs/build-$n.log 2>&1; echo "$n $tree exit $?"; done
