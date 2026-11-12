#!/bin/bash
# X2d chain 1 (nohup): the d78cbfaa403 SBF build, then the replay tool build; one slot at a time.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
X=$W/x2d
bash $X/bin/fv_x2d_job.sh build-d78 3000 $X/st bash $X/bin/fv_x2d_pool_build.sh X2d-build-d78 src-x2d-1
bash $X/bin/fv_x2d_job.sh tool-1 3600 $X/st bash $X/bin/fv_x2d_tool_build.sh
echo done > $X/st/chain1.done
