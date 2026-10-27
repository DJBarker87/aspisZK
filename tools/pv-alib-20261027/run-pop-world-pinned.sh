#!/bin/sh
set -eu
/home/dombarker/.cargo/bin/rustc +nightly-2026-06-01 --version --verbose
/home/dombarker/.cargo/bin/rustc +nightly-2026-06-01 -O --edition=2021 /home/dombarker/project-offloads/codex-pv-alib-20261027/native-pop-world-pinned-02/main.rs -o /home/dombarker/project-offloads/codex-pv-alib-20261027/native-pop-world-pinned-02/pop-world
/home/dombarker/project-offloads/codex-pv-alib-20261027/native-pop-world-pinned-02/pop-world
