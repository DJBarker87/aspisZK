#!/bin/bash
# X2b: write one cumulative `diff -u` patch per changed source file, against the FROZEN file (commit
# 3d700effcabe1dbf2d3ceaa3aaa469fcdfb955de), from a frozen copy and a rewrite-tree copy of the three crates' sources.
# Each patch contains X2's changes to that file as well as X2b's (it supersedes X2's per-function patches for that
# file). Paths in the patch headers are repository-relative (a/<path>, b/<path>).
# Usage: fv_x2b_patches.sh <frozen root> <rewrite root> <out dir>
set -u
F=$1; R=$2; O=$3
mkdir -p $O
cd $R
for f in $(find programs/aspis-pool/src crates/aspis-statement/src crates/aspis-core/src -name '*.rs' | sort); do
  if ! cmp -s $F/$f $R/$f; then
    n=$(echo $f | sed -e 's#^programs/aspis-pool/src/#pool__#' -e 's#^crates/aspis-statement/src/#statement__#' -e 's#^crates/aspis-core/src/#core__#' -e 's#/#__#g' -e 's#\.rs$##')
    diff -u --label a/$f --label b/$f $F/$f $R/$f > $O/$n.patch
    echo "$n.patch $(grep -c '^[-+][^-+]' $O/$n.patch) changed lines"
  fi
done
