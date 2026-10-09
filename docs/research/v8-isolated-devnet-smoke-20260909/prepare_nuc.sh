#!/usr/bin/env bash
# Run once in a fresh task-owned git archive of bc945367; never in a worktree.
set -euo pipefail
readonly demo_dir="$(cd "$(dirname "$0")" && pwd)"
readonly demo_root="$(cd "$demo_dir/../../.." && pwd)"
[[ "$demo_root" == /home/dombarker/project-offloads/aspis-v8-devnet-smoke-20260909 && ! -e "$demo_root/.git" ]]
readonly experiment="$demo_root/docs/research/v8-no-work-100-20260907/experiments"
cd "$demo_root"
bash "$experiment/prepare_complete_nuc.sh"
for patch in qm-channel-partial qm-group-partial terminal-query-sumcheck pool-zero-page; do
  git apply --check --recount --unidiff-zero "$experiment/$patch.patch"
  git apply --recount --unidiff-zero "$experiment/$patch.patch"
done
bash "$experiment/check_terminal_query_sources.sh" terminal-stack
python3 "$demo_dir/prepare_build.py"
python3 "$demo_dir/prepare_prover.py"
python3 "$demo_dir/prepare_checkpoint_receipts.py"
bash "$demo_dir/run_checkpoint_nuc.sh" build-pool "$demo_dir/evidence/reproduced-checkpoint-pool-build.log"
# Cached, offline, optimized SBF/host jobs. Each existing wrapper creates a
# separate MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0 systemd scope.
# Time is expected in compilation only; proof generation is a later live-context job.
bash "$experiment/run_complete_build_nuc.sh" terminal-stack "$demo_dir/evidence/verifier-build.log"
bash "$experiment/run_complete_build_nuc.sh" partial-host "$demo_dir/evidence/prover-build.log"
systemd-run --user --scope --unit=aspis-v8-devnet-tools-build \
  -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v \
  env NO_DNA=1 PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin \
  CARGO_TARGET_DIR="$demo_root/demo-host-target" RUSTFLAGS='--cfg v8_complete -A unexpected_cfgs' \
  cargo build --offline --locked --release --jobs 2 --manifest-path "$demo_dir/tools/Cargo.toml"
