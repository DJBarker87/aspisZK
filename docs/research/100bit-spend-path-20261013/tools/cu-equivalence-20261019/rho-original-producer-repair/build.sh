#!/bin/bash
set -euo pipefail

export PATH=/home/opam/.opam/5.2/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
export OPAM_SWITCH_PREFIX=/home/opam/.opam/5.2
export CAML_LD_LIBRARY_PATH=/home/opam/.opam/5.2/lib/stublibs:/home/opam/.opam/5.2/lib/ocaml/stublibs:/home/opam/.opam/5.2/lib/ocaml
export OCAMLPATH=/work/charon/_build/install/default/lib:/home/opam/.opam/5.2/lib
export DUNE_CACHE=disabled
export AENEAS_VERSION=b59d5188c082f704a418c7cb4e52ad69328002d1+rho-original-borrow-repair-20261020
cd /work/aeneas/src
# Recompile the two repaired units once for a complete final build receipt.
touch interp/InterpExpressions.ml symbolic/SymbolicToPureValues.ml
/usr/bin/time -v -o /out/release-build.time dune build --profile release -j1 main.exe > /out/release-build.log 2>&1
mkdir -p /out/bin
cp _build/default/main.exe /out/bin/aeneas
/out/bin/aeneas -version > /out/version.txt
