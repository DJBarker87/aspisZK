#!/bin/bash
# Aspis translatability pass: which rewrite costs what. ONE fv_slot.sh scope. In one scratch tree (src-tp1-var, one
# SBF target directory) the batch tree's files are put in place, then for each variant its files are laid over them,
# the program is built with the deployed features (fv_build_adapter_src.sh) and the two recorded payments are replayed.
# The difference between the batch and a variant is what that one rewrite costs in the batch's context.
# Usage: [MINI=<probe>] fv_tp1_bisect.sh <tag> <variant>...     variants are directories of tp1/var-<tag>/ (B is the reference itself)
#   MINI=<probe>: first run the second tool pair on the stand-alone crate tp1/mini/<probe> (a construct probe) in the same scope
#   prepared beforehand: src-tp1-var = the restored tree + the batch patch; tp1/var-<tag>/<variant>/ = the files of
#   that variant that differ from the batch tree; tp1/var-<tag>/B/ = the batch tree's own copies of all those files.
# Time is expected in compilation (one cold SBF build, then incremental rebuilds of the two crates).
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
TAG=$1; shift
bash fv_slot.sh TP-B-$TAG 5400 env MINI=${MINI:-} bash $W/fv_tp1_bisect_inner.sh $TAG "$@" > $W/tp1/bisect-$TAG.log 2>&1
echo "scope exit $?"; cat $W/tp1/bisect-$TAG.txt 2>/dev/null | cut -c1-240
