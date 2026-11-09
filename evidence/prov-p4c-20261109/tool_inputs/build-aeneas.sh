#!/bin/bash
set -euo pipefail
while [ ! -f /work/aeneas-go ]; do sleep 0.2; done
export PATH=/home/opam/.opam/5.2/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
export OPAM_SWITCH_PREFIX=/home/opam/.opam/5.2
export CAML_LD_LIBRARY_PATH=/home/opam/.opam/5.2/lib/stublibs:/home/opam/.opam/5.2/lib/ocaml/stublibs:/home/opam/.opam/5.2/lib/ocaml
export OCAMLPATH=/work/charon/_build/install/default/lib:/home/opam/.opam/5.2/lib
export DUNE_CACHE=disabled
export AENEAS_VERSION=b59d5188c082f704a418c7cb4e52ad69328002d1
mkdir -p /work/aeneas-build-a
{
 ocamlopt -version
 dune --version
 ocamlfind printconf
 ocamlfind list
 sha256sum /home/opam/.opam/5.2/bin/ocamlopt /home/opam/.opam/5.2/bin/ocamlc /home/opam/.opam/5.2/bin/dune /home/opam/.opam/5.2/bin/ocamlfind /usr/bin/gcc /usr/bin/ld
 cat /home/opam/.opam/5.2/.opam-switch/switch-state
} > /work/aeneas-build-a/environment.txt 2>&1
cd /work/charon
/usr/bin/time -v -o /work/aeneas-build-a/charon-ml.time dune build --profile release -j1 @install --verbose > /work/aeneas-build-a/charon-ml.log 2>&1
case "$(ocamlfind query charon)" in /work/charon/_build/install/default/lib/charon) ;; *) echo 'Unexpected Charon ML library'; exit 42;; esac
ocamlfind query charon > /work/aeneas-build-a/charon-ml-location.txt
cd /work/aeneas/src
/usr/bin/time -v -o /work/aeneas-build-a/aeneas.time dune build --profile release -j1 main.exe --verbose > /work/aeneas-build-a/aeneas.log 2>&1
mkdir -p /work/bin
cp _build/default/main.exe /work/bin/aeneas
/work/bin/aeneas -version > /work/aeneas-build-a/version.txt
sha256sum /work/bin/aeneas > /work/aeneas-build-a/binary.sha256
