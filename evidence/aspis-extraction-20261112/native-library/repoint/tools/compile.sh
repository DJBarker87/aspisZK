#!/bin/bash
# compile.sh <src_dir> <out_obj_dir> <order_file> <table_out> [extra LEAN_PATH entries AFTER the L187 objects]
# One module at a time, lean -j1 -M7000 -DElab.async=false. Stops on first failure.
set -u
SRC=$1; OUT=$2; ORDER=$3; TAB=$4; EXTRA=${5:-}
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
L187=$HOME/aspis-lead-infra/l187-closure
mkdir -p $OUT $OUT/../logs
LP=$OUT:$L187/objs:$L187/base
[ -n "$EXTRA" ] && LP=$LP:$EXTRA
echo "# LEAN_PATH=$LP" > $TAB
printf 'module\tsha256\texit\twall_s\tpeak_rss_bytes\n' >> $TAB
LOGD=$(dirname $TAB)/logs-$(basename $TAB .tsv); mkdir -p $LOGD
while read m; do
  [ -z "$m" ] && continue
  sha=$(shasum -a 256 $SRC/$m.lean | cut -d' ' -f1)
  t0=$(python3 -c 'import time;print(time.time())')
  ( cd $SRC && LEAN_PATH=$LP /usr/bin/time -l timeout 600 $LEAN -j1 -M7000 -DElab.async=false -o $OUT/$m.olean $m.lean ) > $LOGD/$m.out 2> $LOGD/$m.err
  ec=$?
  t1=$(python3 -c 'import time;print(time.time())')
  rss=$(grep 'maximum resident set size' $LOGD/$m.err | awk '{print $1}')
  wall=$(python3 -c "print(round($t1-$t0,2))")
  printf '%s\t%s\t%s\t%s\t%s\n' $m $sha $ec $wall $rss >> $TAB
  if [ $ec -ne 0 ]; then echo "FAIL $m ($ec)"; exit $ec; fi
done < $ORDER
echo DONE
