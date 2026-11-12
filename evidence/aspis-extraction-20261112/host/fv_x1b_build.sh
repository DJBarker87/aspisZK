#!/bin/bash
# X1b: copy a rewrite tree to W/src-x1b-<n> (everything but target/: the workspace members reference docs/) and build the
# deployed SBF program from it with the lead's fv_frz_build.sh (read only), optionally also the two-transaction
# configuration. Runs INSIDE one fv_slot.sh scope. Usage: fv_x1b_build.sh <tree under W/x1b> <n> [aspis|both]
set -u
W=/home/dombarker/project-offloads/future-version-20261111; TREE=$1; N=$2; WHICH=${3:-aspis}
P=37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt; R=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q
D=$W/src-x1b-$N; test ! -e $D || { echo "exists: $D"; exit 2; }
mkdir -p $D && (cd $W/x1b/$TREE && tar cf - --exclude=./target .) | (cd $D && tar xf -)
bash $W/fv_frz_build.sh X1b-$N src-x1b-$N aspis $P $R > $W/x1b/logs/build-$N.log 2>&1; echo "aspis exit $?"; cat $W/out/X1b-$N/so.sha256
if [ $WHICH = both ]; then
  bash $W/fv_frz_build.sh X1b-$N-2tx src-x1b-$N pool-adapter,private-leaf-salts $P $R > $W/x1b/logs/build-$N-2tx.log 2>&1; echo "2tx exit $?"; cat $W/out/X1b-$N-2tx/so.sha256
fi
