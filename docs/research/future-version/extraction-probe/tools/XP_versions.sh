#!/bin/bash
# Aspis extraction probe: print tool versions (inside an fv_slot.sh scope).
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
S=/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin
F=/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin
echo "second charon: $($S/charon version 2>&1 | head -3)"; echo "second charon toolchain-path: $($S/charon toolchain-path 2>&1 | head -3)"
echo "first charon: $($F/charon version 2>&1 | head -3)"; echo "first charon toolchain-path: $($F/charon toolchain-path 2>&1 | head -3)"
echo "second aeneas: $($S/aeneas -version 2>&1 | head -3)"; echo "first aeneas: $($F/aeneas-b59d5188-extended -version 2>&1 | head -3)"
RUSTUP_TOOLCHAIN=nightly-2026-09-17 rustc -Vv | head -6; cargo +nightly-2026-09-17 -V
$S/charon cargo --help 2>&1 | head -80
