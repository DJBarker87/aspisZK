#!/bin/bash
cd /Users/dominic/ZK/.worktrees/pc-prov-p2h/evidence/prov-p2h-20261109
f=$1/stdout.log; if [ -f $f ]; then cat $f; else xzcat $f.xz; fi
