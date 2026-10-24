#!/usr/bin/env bash
set -euo pipefail
export OCAMLPATH="/prior-deps/lib:${OCAMLPATH:-}"
export AENEAS_VERSION=b59d5188-lean432-extended
export OCAMLPARAM=_,ccopt=-static
cd /job/base/src
dune build main.exe --profile release -j 4
sha256sum _build/default/main.exe > /job/base-binary.sha256
