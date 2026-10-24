#!/usr/bin/env bash
set -euo pipefail
cd /job/charon
opam list --installed --columns=name,version > /job/opam-packages.txt
ocamlc -version > /job/ocaml-version.txt
dune --version > /job/dune-version.txt
dune build @install --profile release -j 4
dune install --prefix /job/deps
export OCAMLPATH="/job/deps/lib:${OCAMLPATH:-}"
export AENEAS_VERSION=b59d5188-lean432-extended-ProverRwRngExtractor
export OCAMLPARAM=_,ccopt=-static
cd /job/base/src
dune build main.exe --profile release -j 4
sha256sum _build/default/main.exe > /job/base-binary.sha256
