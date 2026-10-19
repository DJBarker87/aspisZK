set -e
cd /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/src
export CARGO_TARGET_DIR=/home/dombarker/project-offloads/codex-r1-pool-pda-20261019/sbf-target CARGO_HOME=/home/dombarker/.cargo PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_NET_OFFLINE=true
SOL=/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf
mkdir -p /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/artifacts/pool
python3 /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/harness/capped.py /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/receipts/sbf-pool-3 "SBF compile/link of Pool only; attempts 1-2 failed at cargo metadata: z4 and c3 path dependencies missing from the archive" -- $SOL --manifest-path /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/src/programs/aspis-pool/Cargo.toml --sbf-out-dir /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/artifacts/pool --features r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit --skip-tools-install --offline -j 4 -- --locked
cp /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/sbf-target/sbpf-solana-solana/release/aspis_pool.so /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/artifacts/pool/linked.elf
sha256sum /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/artifacts/pool/aspis_pool.so /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/artifacts/pool/linked.elf
stat -c '%n %s' /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/artifacts/pool/aspis_pool.so /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/artifacts/pool/linked.elf
