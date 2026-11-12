#!/bin/bash
# X2c: one cumulative `diff -u` per changed source file of the Pool, aspis-statement and aspis-core crates, against the
# frozen file (new files against /dev/null). Light (no slot needed).
# Usage: fv_x2c_patches.sh <frozen root> <rewrite root> <out dir>
#   roots hold programs/aspis-pool/src and crates/{aspis-statement,aspis-core}/src (or, locally, aspis-pool/src etc.)
set -u
F=$1; R=$2; O=$3; mkdir -p $O
for d in programs/aspis-pool/src crates/aspis-statement/src crates/aspis-core/src; do
  [ -d $R/$d ] || continue
  ( cd $R && find $d -name '*.rs' | sort ) | while read f; do
    pre=$(echo $d | sed 's#programs/aspis-pool/src#pool#; s#crates/aspis-statement/src#statement#; s#crates/aspis-core/src#core#')
    rel=${f#$d/}; name="${pre}__$(echo ${rel%.rs} | sed 's#/#__#g').patch"
    if [ -f $F/$f ]; then
      cmp -s $F/$f $R/$f && continue
      diff -u --label a/$f --label b/$f $F/$f $R/$f > $O/$name
    else
      diff -u --label /dev/null --label b/$f /dev/null $R/$f > $O/$name
    fi
    echo "$name $(grep -c '^[+-][^+-]' $O/$name) changed lines"
  done
done
