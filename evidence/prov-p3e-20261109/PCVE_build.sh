#!/bin/bash
# usage: bash PCVE_build.sh OUTNAME tail1.lean [tail2.lean ...]   (assembles head + helpers + lemmas + tails)
cd "$(dirname "$0")"
out=$1; shift
cat PCVE_head.lean PCVE_helpers.lean PCVE_lemmas.lean "$@" > "$out.lean"
wc -l "$out.lean"
