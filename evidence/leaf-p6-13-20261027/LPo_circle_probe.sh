#!/bin/sh
set -eu
/home/dombarker/.cargo/bin/rustc --version
/home/dombarker/.cargo/bin/rustc --edition=2024 -Awarnings -C opt-level=3 -C debuginfo=0 LPo_circle_probe.rs -o LPo_circle_probe
./LPo_circle_probe
