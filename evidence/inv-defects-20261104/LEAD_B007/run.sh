set -euo pipefail
B=/home/dombarker/project-offloads/codex-cx-inv-defects-20261104; L=$B/LEAD_B007
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
export CARGO_BUILD_JOBS=1 CARGO_NET_OFFLINE=true CARGO_INCREMENTAL=0 CARGO_PROFILE_DEV_DEBUG=0
export RUSTFLAGS="-C codegen-units=1"
unset RUSTC_WRAPPER
sha256sum $B/NFZ_src/Cargo.lock | tee $L/lock-before.sha256
/usr/bin/time -v cargo +1.94.1 rustc --manifest-path $B/NFZ_src/programs/r1-cost-probe/Cargo.toml -p aspis-statement --locked --offline --lib -j1 --target-dir $B/LEAD_B006/target -- --emit=mir -C codegen-units=1
sha256sum $B/NFZ_src/Cargo.lock | tee $L/lock-after.sha256
ls $B/LEAD_B006/target/debug/deps/aspis_statement*.mir
