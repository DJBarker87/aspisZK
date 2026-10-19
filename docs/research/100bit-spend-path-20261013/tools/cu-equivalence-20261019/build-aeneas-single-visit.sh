#!/bin/bash
set -euo pipefail
while [ ! -f /out/compile-go ]; do sleep 0.2; done
export PATH=/home/opam/.opam/5.2/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
export OPAM_SWITCH_PREFIX=/home/opam/.opam/5.2
export CAML_LD_LIBRARY_PATH=/home/opam/.opam/5.2/lib/stublibs:/home/opam/.opam/5.2/lib/ocaml/stublibs:/home/opam/.opam/5.2/lib/ocaml
export OCAMLPATH=/work/charon/_build/install/default/lib:/home/opam/.opam/5.2/lib
export DUNE_CACHE=disabled
export AENEAS_VERSION=b59d5188c082f704a418c7cb4e52ad69328002d1+single-visit-20261019
cd /work/aeneas/src
/usr/bin/time -v -o /out/compile-time.log dune build --profile release -j1 main.exe > /out/compile.log 2>&1
mkdir -p /out/bin
cp _build/default/main.exe /out/bin/aeneas
/out/bin/aeneas -version > /out/version.txt
