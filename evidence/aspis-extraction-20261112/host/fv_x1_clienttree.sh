#!/bin/bash
# X1: resolved features of aspis-core, aspis-r1-cost-probe, aspis-statement in the client configuration
# (tools/r1-cost-probe --features r1p-check), host target. Reads only; output W/x1/tree-client.
set -u
W=/home/dombarker/project-offloads/future-version-20261111; O=$W/x1/tree-client; mkdir -p $O
cd $W/src-frz-a/tools/r1-cost-probe
env PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_TARGET_DIR=$W/x1/target/tree-client CARGO_NET_OFFLINE=true cargo tree --locked --offline --features r1p-check -e normal --prefix none -f "{p}|{f}" > $O/pkgfeatures.txt 2>&1; echo "exit $?" >> $O/exit.txt
