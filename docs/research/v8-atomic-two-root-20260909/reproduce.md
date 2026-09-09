**Reproduction and retained resources**

The local worktree is `/Users/dominic/ZK/.worktrees/ZK-v8-atomic-two-root-20260909`, branch `research/v8-atomic-two-root-20260909`. Only this research directory is changed. The pinned Linux build copy is `/home/dombarker/project-offloads/aspis-v8-atomic-two-root-20260909` on the already authorized `dombarker@nuc.local`. It is an archive, not another moving branch. Scripts deliberately reject other root paths. Do not replace that guard with an existing worker's copy.

Local, inexpensive checks (Python standard library only):

```sh
python3 -m unittest discover -s docs/research/v8-atomic-two-root-20260909 -p model.py -v
python3 docs/research/v8-atomic-two-root-20260909/audit_results.py --check
python3 docs/research/v8-atomic-two-root-20260909/audit_source.py
bash -n docs/research/v8-atomic-two-root-20260909/build.sh docs/research/v8-atomic-two-root-20260909/run_matrix.sh
git diff --check
```

`audit_results.py` checks the retained nine final JSON files, independently reconstructs B, compares all identical proof hashes and single-root CU with terminal-query-results.json, parses every signed TxV1 configuration, and verifies rollback/fee evidence. It writes measurements.json only without `--check`. `audit_source.py` reconstructs the four permitted archive overlays in a disposable temporary source directory and checks all 429 captured source files. It creates no wallet keys and runs no compiler.

For a specifically justified runtime replay in the preserved Linux copy, inspect current reservations first; do not repeat unchanged suites just because documentation changed:

```sh
ssh dombarker@nuc.local
cd /home/dombarker/project-offloads/aspis-v8-atomic-two-root-20260909
free -h
systemctl --user list-units --type=scope --state=running
python3 docs/research/v8-atomic-two-root-20260909/artifact_guard.py check
bash docs/research/v8-atomic-two-root-20260909/run_matrix.sh /tmp/aspis-atomic-NEW-evidence
```

Choose a genuinely fresh output path. The script runs six maximum-body deep cases and three freshly generated ordinary proof cases, serially, in 3-GiB-high/4-GiB-max scopes with zero swap. Each output contains the full signed transaction wire, instruction account metas/data, CPI trace, explicit configuration, CU, protected-state hashes and fee delta. Its `1400000` positional argument matches the inherited driver's default and therefore avoids its diagnostic runtime-budget override. The actual signed TxV1 gate is hard-coded to 1,200,000 and independently decoded from wire bytes. Do not treat the positional argument as the gate.

The original archive was created with this source selection, only after inspecting instructions, branches, worktrees, dirty files, remote heads and resource availability. These commands are preparation documentation, not instructions to overwrite the preserved copy:

```sh
git archive 4aaa61e679189b2cf76bfc25c2e3ff8d5c76341e \
  AGENTS.md Cargo.toml Cargo.lock crates programs \
  docs/research/v8-no-work-100-20260907 \
  results/v7-pair-forest-combined-rejection-litesvm-20260828 \
  | ssh dombarker@nuc.local 'test ! -e /home/dombarker/project-offloads/aspis-v8-atomic-two-root-20260909 && mkdir /home/dombarker/project-offloads/aspis-v8-atomic-two-root-20260909 && tar -x -C /home/dombarker/project-offloads/aspis-v8-atomic-two-root-20260909'
rsync -a docs/research/v8-atomic-two-root-20260909/ \
  dombarker@nuc.local:/home/dombarker/project-offloads/aspis-v8-atomic-two-root-20260909/docs/research/v8-atomic-two-root-20260909/
```

In that **fresh** archive, `prepare_build.py` checks the source manifest before patching, checks immutable predecessor artifact/proof hashes, applies only complete-integration, complete-matched-driver, pool-zero-driver and token-control-driver, and independently copies the existing SBF/host-driver caches using reflinks where possible. It never hard-links caches or writes the predecessor. `install_driver.py` requires the exact resulting baseline driver hash and adds the isolated module/hook and explicit TxV1 feature activation. Root/default workspaces stay untouched. Then use `build.sh inbox NEW.log`, `build.sh driver NEW.log`, and `build.sh prover NEW.log` from this directory. Each build is optimized/offline/locked, jobs=2, MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0. `build-inputs.json` freezes the measured source/executable/fixture closure; a reproduction must match it or report the drift rather than silently accepting another build. The first original inbox resolution created the now-retained Cargo.lock; subsequent reproduction requires it. The retained verifier/Pool/Registry are hash-pinned ELFs from the selected predecessor, not rebuild claims for unrecorded arithmetic overlays.

The original fresh ordinary proving commands, from the task-owned Linux root, were:

```sh
mkdir -p proving/context proving/proofs
systemd-run --user --scope --unit=aspis-atomic-context-NEW \
  -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 /usr/bin/time -v \
  env ASPIS_V8_EXPORT_CONTEXT="$PWD/proving/context" \
  docs/research/v8-no-work-100-20260907/experiments/performance-svm/target/release/aspis-v7-pair-forest-combined-rejection \
  artifacts/pool.so artifacts/verifier.so artifacts/registry.so artifacts/double.so \
  proving/unused.json fixtures/transfer-13-1.bin success 1400000 asq8 13 transfer
systemd-run --user --scope --unit=aspis-atomic-proving-NEW \
  -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 /usr/bin/time -v \
  env -u ASPIS_V8_MAX_FRONTIER_SCAN ASPIS_V8_COMPLETE_CONTEXT="$PWD/proving/context" \
  docs/research/v8-no-work-100-20260907/experiments/performance-host/target/release/aspis-v8-performance-host \
  proving/proofs
```

The first command exports synthetic authoritative context without a transition or proof acceptance. The second generates three ordinary proofs without diagnostic nonce searches. Do not run these commands over the retained evidence/proofs; use fresh paths for a justified changed experiment. Maximum-body proofs are copied by exact hash from the existing retained diagnostic fixture set, not regenerated through a new expensive search. `artifact_guard.py capture` was used once to freeze the completed measured copy; normal replay uses `check` and refuses drift.

No ELF, secret note opening, witness dump or key file is committed here. Deterministic synthetic LiteSVM keys remain reconstructible from the inherited fixture source; generated build keys remain in the task-owned Linux copy. None controls network funds or was used to send a network transaction. No deployment, proof upload, seal, cleanup, push or merge command is part of this reproduction.
