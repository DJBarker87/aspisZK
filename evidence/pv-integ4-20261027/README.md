# D325 merged candidate integration gates

Source `03905a52594fadc50a1c00ab3f240a79632e8ffd`; branch `codex/pv-integ4-20261027`. No implementation source edits. Target not yet established.

Stages pending. Timing gate is expressly not authorized for this job. All native builds use serial capped scopes (6G/8G, swap0, TasksMax64), optimized -j4; preflight and in-scope admission require allowed:true and exit0. IDs39500–39599 reserved but no Lean compilation planned. Kani0.

## Stage 1: verifier ELFs — PASS

Fresh candidate rebuilds match all three requested SHA256 pins; see `elf-summary.json` and per-build receipts. Default 1,563,728 bytes,54.250s,684,548KiB RSS; devnet 1,563,728 bytes,35.294s,685,392KiB; Pool605,704 bytes,47.509s,677,856KiB. All exit0/swap0. The initial default launch failed before compilation on a non-executable job-local diagnostic wrapper; mode corrected, distinct retry receipt retained. No pin mismatch. `source-identity.json` verifies every exported input (7,290 files) against exact git source bytes.

## Stage 2: pinned client and route — PASS

**recipe features pending owner approval; toolchain pinned 1.94.1**

Client SHA256 `3a1b03d0eb2bbffb59631631d065d7a0dda2a57e5ca3e36d782abe49540b2ffa`,2,852,008 bytes. Exact command from `source/tools/r1-cost-probe`: `cargo build --release --offline --locked -j 4 --features r1p-check,aspis-r1-cost-probe/ct-host-prover --bin devnet_spend`. `build-client/rustc-vV.txt` records rustc1.94.1(e408947bfd200af42db322daf0fadfe7e26d3bd1),LLVM21.1.8,x86_64-unknown-linux-gnu. Compile exit0,111.512s,644,252KiB RSS,swap0. Named toolchain auto-installed before compilation.

`client-route-summary.json` and `binary-route/route-symbols.json` retain resolved direct/GOT paths from main to generate_for_mask_nonce and to op223, batch1 helper_sum/powers, batch2 sampler/weights, and batch3 public/terminal/multilinear/copy/forest symbols. prover.rs:349 and sim.rs:341 retain batch1 prover_powers. ct_pole is inlined; its selected callsite is source-pinned, not claimed as a standalone symbol. Simulator callsites are source-inspected rather than reachable from this client main. Full disassembly remains host-side with its hash; selected disassembly and relocation evidence are committed. Static route association is not a universal source/model proof.
