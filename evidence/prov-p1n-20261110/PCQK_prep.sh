#!/bin/bash
# usage: bash PCQK_prep.sh RUN STABLE_NAME : pre-create host symlink <run>_emitted/repro.llbc -> PCQK_stable/<name>.llbc (PCVV_E006)
B=/home/dombarker/project-offloads/codex-pc-prov-p1n-20261110
ssh -o ConnectTimeout=20 -o ServerAliveInterval=15 dombarker@100.108.41.90 "timeout 60 bash -c 'mkdir -p $B/PCQK_stable $B/$1_emitted && ln -sfn $B/PCQK_stable/$2.llbc $B/$1_emitted/repro.llbc'"
