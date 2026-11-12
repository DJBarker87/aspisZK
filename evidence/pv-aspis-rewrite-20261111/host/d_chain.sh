#!/bin/bash
# Gate D chain: translate each named root set in turn. usage: d_chain.sh NAME SRCDIR TAG...
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111
N=$1; export PV_SRC_DIR=$2; shift 2
for t in "$@"; do bash $W/tools/translate.sh $t; done
echo done > $W/D_CHAIN_$N.DONE
