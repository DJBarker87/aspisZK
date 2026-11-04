set -euo pipefail
B=/home/dombarker/project-offloads/codex-cx-inv-defects-20261104; L=$B/LEAD_B006
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
export CARGO_BUILD_JOBS=1 CARGO_NET_OFFLINE=true CARGO_INCREMENTAL=0 CARGO_PROFILE_DEV_DEBUG=0
export RUSTFLAGS="-C codegen-units=1"
unset RUSTC_WRAPPER
cd $B/NFZ_src && git rev-parse HEAD 2>/dev/null || true
sha256sum $B/NFZ_src/Cargo.lock | tee $L/lock-before.sha256
/usr/bin/time -v cargo +1.94.1 rustc --manifest-path $B/NFZ_src/programs/r1-cost-probe/Cargo.toml -p aspis-r1-cost-probe-program --locked --offline --features pool-adapter,private-leaf-salts --lib -j1 --target-dir $L/target -- --emit=mir -C codegen-units=1
sha256sum $B/NFZ_src/Cargo.lock | tee $L/lock-after.sha256
ls $L/target/debug/deps/*.mir
