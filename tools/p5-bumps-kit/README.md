# Frozen P5 component proofs

- `python3 inventory.py`: regenerate the conservative frozen source census.
- `python3 prepare.py --check`: check every generated declaration/slice/constant.
- `prepare.py` writes only this isolated tool crate, never shipped programs.
- Host workspace: `/home/dombarker/project-offloads/codex-cx-p5-bumps-20261021`.
- Kani 0.67.0. Generated Cargo profiles use opt-level=3, overflow checks on.
- Every attempt: its own user systemd scope, MemoryHigh=6G, MemoryMax=8G,
  MemorySwapMax=0, TasksMax=64. `CARGO_BUILD_JOBS=4`; 180-second proof deadline.
- `capped.py` refuses an existing receipt directory and asserts actual cgroup caps.
- Before reusing `run-host.py`, allocate fresh receipt numbers and inspect the
  recorded source/dependency fingerprints. Do not rerun unchanged proof inputs.
- The exact scope/limitations are in the P5 design document. In particular,
  reduced type contexts and source slices are not an extracted whole program.
- No wallet/key, shipped source, ELF, S1/S3/S4/S5/S9/S10 re-pin or M10 file is touched.
