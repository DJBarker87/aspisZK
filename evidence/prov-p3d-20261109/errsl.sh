#!/bin/bash
cd /Users/dominic/ZK/.worktrees/pc-prov-p3d/evidence/prov-p3d-20261109
xz -dc $1/stdout.log.xz | awk '/error/{p=1} /warning/{p=0} /^\x27PRV/{print; p=0} p{print}' | cut -c1-300 | head -${2:-80}
