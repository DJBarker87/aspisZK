set -e
cd /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/src
export CARGO_TARGET_DIR=/home/dombarker/project-offloads/codex-r1-pool-pda-20261019/sbf-target-clean CARGO_HOME=/home/dombarker/.cargo PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_NET_OFFLINE=true
SOL=/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf
mkdir -p /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/artifacts/pool-clean
python3 /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/harness/capped.py /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/receipts/sbf-pool-clean "clean (empty target dir) SBF compile of Pool for a complete stack-diagnostic inventory; 2-6 min" -- $SOL --manifest-path /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/src/programs/aspis-pool/Cargo.toml --sbf-out-dir /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/artifacts/pool-clean --features r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit --skip-tools-install --offline -j 4 -- --locked
mkdir -p /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/stack
cp /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/sbf-target-clean/sbpf-solana-solana/release/aspis_pool.so /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/stack/linked.elf
cp /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/artifacts/pool-clean/aspis_pool.so /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/stack/stripped.so
cp /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/receipts/sbf-pool-clean/stderr.log /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/stack/build.log
sha256sum /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/stack/linked.elf /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/stack/stripped.so /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/artifacts/pool/aspis_pool.so
python3 /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/harness/capped.py /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/receipts/stack-audit "strict linked-ELF stack audit (python, seconds)" -- python3 /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/harness/pool-strict-stack.py /home/dombarker/project-offloads/codex-r1-pool-pda-20261019/stack
