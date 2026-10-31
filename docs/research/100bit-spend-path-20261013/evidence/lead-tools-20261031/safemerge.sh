#!/bin/bash
# usage: safemerge.sh <branch> <message>
# Merge a worker branch into research WITHOUT running `git merge` in the shared checkout:
# merge-tree -> commit-tree -> guarded update-ref -> restore only the changed paths.
# Refuses on conflicts, blobs > 20 MB, a lock, or any changed path that is dirty in the shared checkout.
set -e
R=/Users/dominic/ZK; B=$1; MSG=$2; cd $R
OLD=$(git rev-parse research); BH=$(git rev-parse $B)
T=$(git merge-tree --write-tree $OLD $BH) || { echo "CONFLICT"; exit 1; }
BIG=$(git rev-list --objects $(git merge-base $OLD $BH)..$BH | git cat-file --batch-check='%(objecttype) %(objectsize) %(rest)' | awk '$1=="blob" && $2>20000000')
[ -z "$BIG" ] || { echo "BIG BLOBS: $BIG"; exit 1; }
CH=$(git diff --name-only $OLD $T)
DIRTY=$(git status --porcelain --untracked-files=no | cut -c4-)
X=$(comm -12 <(echo "$CH" | sort) <(echo "$DIRTY" | sort))
[ -z "$X" ] || { echo "DIRTY OVERLAP: $X"; exit 1; }
C=$(git commit-tree $T -p $OLD -p $BH -m "$MSG")
test ! -e .git/index.lock || { echo LOCKED; exit 1; }
git update-ref refs/heads/research $C $OLD
echo "$CH" > /Users/dominic/.claude/jobs/39d1fe54/tmp/safemerge_paths.txt
git restore --source=$C --staged --worktree --pathspec-from-file=/Users/dominic/.claude/jobs/39d1fe54/tmp/safemerge_paths.txt
git log --oneline -1
