#!/bin/sh
set -eu
d=/home/dombarker/project-offloads/codex-pv-relink-20261028
for row in v178 v179 v182; do sh "$d/run-std.sh" "$row"; done
