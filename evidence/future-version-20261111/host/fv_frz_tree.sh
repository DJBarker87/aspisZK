#!/bin/bash
# Aspis freeze: make a source tree on the host whose crates/, programs/, tools/, Cargo.toml and Cargo.lock are
# exactly those of one commit. The archive of those paths (git archive <commit> crates programs tools Cargo.toml
# Cargo.lock) is read from stdin. Everything else a build needs and the commit does not change (the workspace
# members under audit/, xtask/ and docs/) is copied from src-cand1.
# Usage: git archive <commit> crates programs tools Cargo.toml Cargo.lock | ssh host bash fv_frz_tree.sh <name> <commit>
set -eu
W=/home/dombarker/project-offloads/future-version-20261111
N=$1; C=$2
test ! -e $W/$N || { echo "exists: $W/$N"; exit 2; }
T=$(mktemp -d $W/frz-tree.XXXXXX); cat > $T/src.tar
sha256sum $T/src.tar | cut -d' ' -f1 > $T/src.tar.sha256
cp -a $W/src-cand1 $W/$N
rm -rf $W/$N/crates $W/$N/programs $W/$N/tools $W/$N/Cargo.toml $W/$N/Cargo.lock
tar xf $T/src.tar -C $W/$N
echo "$C" > $W/$N/FROZEN_COMMIT; cp $T/src.tar.sha256 $W/$N/FROZEN_ARCHIVE_SHA256
( cd $W/$N && find crates programs tools -type f | sort | xargs sha256sum | sha256sum | cut -d' ' -f1 ) > $W/$N/FROZEN_TREE_SHA256
rm -rf $T
echo "$N: commit $C, archive sha256 $(cat $W/$N/FROZEN_ARCHIVE_SHA256), files sha256 $(cat $W/$N/FROZEN_TREE_SHA256), $(cd $W/$N && find crates programs tools -type f | wc -l) files"
