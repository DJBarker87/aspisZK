#!/bin/bash
# PCWH phase 2 (runs in the pinned image r3, container cgroup capped 6G/8G swap 0 by the host controller; network ENABLED for opam).
# Newest pair: Aeneas 0d21a9ec + Charon 454586e9 (charon-pin). The image's opam switch has visitors 20250212 / ppxlib 0.35 / ppx_deriving 6.0.3 and
# no ppx_deriving_hash; the new Charon needs visitors >= 20260520, ppx_deriving_hash >= 0.1.5. Dry-run first; in-place upgrade if small,
# else a fresh switch (recorded in the log, branch chosen by the script).
set -uo pipefail
while [ ! -f /work/aeneas-go ]; do sleep 0.2; done
export PATH=/home/opam/.opam/5.2/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
export OPAMYES=1 OPAMCOLOR=never OPAMJOBS=2 DUNE_CACHE=disabled HOME=/home/opam
L=/work/pair-build; mkdir -p $L; exec > >(tee -a /work/pair-build.log) 2>&1
echo "== start $(date -u +%FT%TZ)"
ocamlopt -version; dune --version; opam --version
sha256sum /home/opam/.opam/5.2/bin/ocamlopt /home/opam/.opam/5.2/bin/dune
opam repo set-url default https://opam.ocaml.org 2>&1 | tail -3
opam update 2>&1 | tail -5
opam repo list
opam install --dry-run visitors.20260520 ppx_deriving_hash.0.1.5 > $L/dry.log 2>&1; echo "dry exit $?"
tail -40 $L/dry.log
N=$(grep -c -E '(install|upgrade|recompile|downgrade|remove) ' $L/dry.log || true)
echo "dry-run action lines: $N"
if [ "$N" -le 45 ] && grep -q 'visitors' $L/dry.log; then
  echo "BRANCH in-place"
  opam install -j2 visitors.20260520 ppx_deriving_hash.0.1.5 > $L/install.log 2>&1; rc=$?; echo "install exit $rc"; tail -15 $L/install.log
  [ $rc -eq 0 ] || exit 51
else
  echo "BRANCH fresh-switch"
  opam switch create pcwh ocaml-base-compiler.5.2.1 > $L/switch.log 2>&1 || { tail -20 $L/switch.log; exit 52; }
  eval $(opam env --switch=pcwh)
  opam install -j2 dune.3.24.2 menhir ppxlib.0.37.0 ppx_deriving ppx_deriving_yojson ppx_deriving_hash.0.1.5 visitors.20260520 yojson zarith unionFind logs calendar domainslib easy_logging ocamlgraph progress re > $L/install.log 2>&1; rc=$?; echo "install exit $rc"; tail -15 $L/install.log
  [ $rc -eq 0 ] || exit 53
fi
opam list --installed 2>/dev/null | grep -E '^(visitors|ppxlib|ppx_deriving|ppx_deriving_hash|ppx_deriving_yojson|dune|yojson|zarith|menhir|ocaml-base-compiler) ' 
export OCAMLPATH=/work/charon/_build/install/default/lib:$(opam var lib)
cd /work/charon
/usr/bin/time -v -o $L/charon-ml.time dune build --profile release -j2 @install > $L/charon-ml.log 2>&1; rc=$?; echo "charon-ml exit $rc"; tail -20 $L/charon-ml.log
[ $rc -eq 0 ] || exit 54
cd /work/aeneas/src
export AENEAS_VERSION=0d21a9ec7bbbb110110cacc14464a47fd71c8705
/usr/bin/time -v -o $L/aeneas.time dune build --profile release -j2 main.exe > $L/aeneas.log 2>&1; rc=$?; echo "aeneas exit $rc"; tail -20 $L/aeneas.log
[ $rc -eq 0 ] || exit 55
mkdir -p /work/bin; cp _build/default/main.exe /work/bin/aeneas
/work/bin/aeneas -version > $L/version.txt 2>&1; cat $L/version.txt
sha256sum /work/bin/aeneas > $L/binary.sha256; cat $L/binary.sha256
opam list --installed > $L/opam-installed.txt 2>&1
echo "== done $(date -u +%FT%TZ)"
