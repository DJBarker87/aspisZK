#!/bin/bash
set -euo pipefail
opam list --installed --columns=name,version > /job/current-opam-packages.txt
ocamlc -version > /job/current-ocaml-version.txt
dune --version > /job/current-dune-version.txt
cd /job/charon
dune build @install --profile release -j 4
dune install --prefix /job/deps
export OCAMLPATH="/job/deps/lib:${OCAMLPATH:-}"
export AENEAS_VERSION=b59d5188-lean432-extended
export OCAMLPARAM=_,ccopt=-static
cd /job/aeneas/src
dune build main.exe --profile release -j 4
sha256sum _build/default/main.exe > /job/rebuild-binary.sha256
