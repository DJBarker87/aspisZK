#!/bin/bash
# Local side: copy the working tree's build inputs to the host source directory (no deletion).
cd /Users/dominic/ZK/.worktrees/pv-aspis-rewrite && rsync -rlc --itemize-changes --exclude target crates programs tools docs/research/v8-r0-zk-20261009 xtask audit .cargo Cargo.toml Cargo.lock --relative dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/${1:-src}/
