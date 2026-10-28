#!/bin/sh
set -eu
d=/home/dombarker/project-offloads/codex-pv-relink-20261028
for row in v195 v233; do sh "$d/run-cargo.sh" "$row"; done
