#!/bin/bash
# usage: bash showl.sh PCVD_Lnnn [lines]   errors + axioms
cd /Users/dominic/ZK/.worktrees/pc-prov-p3d/evidence/prov-p3d-20261109
xz -dc $1/stdout.log.xz | grep -v "^$" | head -${2:-60}
