# R493 slice length builtin alias candidate

This isolated Aeneas tool build adds the exact source-name matcher alias requested by the lead so the monomorphized `core::slice::{[@T]}::len<@T>` name can match the existing `Slice.len` builtin. The existing `core::slice::{[@T]}::len` registration remains unchanged. The R491 arity fix in `PrePasses.ml` is included unchanged. No translation or Lean compilation was run, and this build establishes no native slice-validity or metadata-adequacy claim.

## Source and change identity

- Pinned source revision: `56a931fc3879354a2fa584e73bd0a1d412714851`
- Release-launch revision: `078a3bd7d4471a5f10549843e7818b956163bb77`
- Isolated build workspace: `/home/dombarker/project-offloads/aspis-r490-slice-len-builtin-20261003-a`
- Baseline `ExtractBuiltinLean.ml`: SHA256 `49eeda5d7dbf34819b9f4663fe8f2bdd276cafc0b6bf18ec00829772d700be0d`
- Candidate `ExtractBuiltinLean.ml`: SHA256 `7963be0b32879555b88960d61d5593780261f82950d06054437cbdb144a5bd16`
- Diff: exactly one added adjacent line, recorded in `ExtractBuiltinLean.diff`.
- Preserved R491 `PrePasses.ml`: SHA256 `587ab22f412f7344aa616cbda35d47bcdaf51492e7e79caaf0ab3bc4279a7eee`
- Cached R491 executable before build: SHA256 `66b70542419d9df6040e0b57aaca3b74896de410d158bccba8274e21fdfc54c1`
- Candidate executable: `/home/dombarker/project-offloads/aspis-r490-slice-len-builtin-20261003-a/aeneas-r493-slice-len-builtin-candidate`
- Candidate executable SHA256: `c8562f6354832214639c5325ca0cc586ada9671189395c19a6fd6f37a7bdabee`

## Build result

- Exact target: `main.exe`
- Command: `AENEAS_VERSION=aspis-r493-slice-len-builtin-20261003-a OCAMLPARAM=_,ccopt=-static opam exec -- dune build main.exe --profile release -j 1`
- Exit status: 0
- Wall time: 1:23.56
- GNU time maximum RSS: 566100 KiB
- Swap events: 0
- Docker cgroup peak memory: 655966208 bytes
- Docker cgroup swap peak: 0 bytes
- Outer systemd scope: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`
- Docker scope: 5G reservation, 7G memory and swap limit (no swap), 128 pids, network disabled
- Aggregate reservation preflight: 22682796032 bytes of 42949672960 maximum
- Docker image: `sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7`
- Translation or Lean compile: not run

Machine-readable preflight, command, result, compiler timing, Docker inspection, and cgroup samples are in `evidence/r493-slice-len-builtin-build/`.
