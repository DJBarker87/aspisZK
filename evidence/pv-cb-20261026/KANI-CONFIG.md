# Kani configuration diagnosis — resume 4

Historical failure: compiler thread creation, before CBMC verification.

```text
thread 'coordinator' (1884512) panicked at /rustc-dev/53732d5e076329a62f71d3c6901886ce8a71e812/compiler/rustc_codegen_ssa/src/back/write.rs:1865:6:
failed to spawn work thread: Os { code: 11, kind: WouldBlock, message: "Resource temporarily unavailable" }
note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace

```

Kani cargo plugin 0.67.0; bundled `kani-compiler --version`: `rustc 1.93.0-nightly (53732d5e0 2025-11-20)`. Ambient default is stable; it is not attributed as Kani’s compiler.

Probe 1 (`kani-config-001`): dependency-free arbitrary-u8 wrapping identity, original TasksMax64, 6G/8G/swap0 and `-j 4`: PASS. The historical failure was not reproduced on this trivial harness. No claim of a deterministic reproduction or repair is made. Exact receipt and log retained.

Probe cargo invocation:

```sh
CARGO_TARGET_DIR=/home/dombarker/project-offloads/codex-pv-cb-20261026/config-target RUSTFLAGS="--cfg kani" /home/dombarker/.cargo/bin/cargo kani --manifest-path /home/dombarker/project-offloads/codex-pv-cb-20261026/config-probe/Cargo.toml --lib --harness config_probe --solver kissat --output-format terse -j 4
```

Configuration mitigation in this job only: `taskset --cpu-list 0-3` before the existing command limits compiler CPU fanout without increasing TasksMax, memory, swap, jobs, timeout or verification bounds. `kani-resume4-circle-001` retries the original non-timeout harness with this changed environment. Compiler stage completed in 19.29s; the gate then timed out at 180s (exit124) in CBMC, with no compiler ICE or verification verdict. This mitigates the observed configuration failure for this run; it does not prove the source row. The timed-out property will not be rerun unchanged. Shared launcher and shared installs untouched.

Update: dependency-matched trivial reproduction

`kani-config-002` uses the same arbitrary-u8 identity, now with the original
aspis-core/aspis-r1-cost-probe dependency graph and a cold own config-target,
original unrestricted host CPU affinity, TasksMax64 and -j4. It reproduces
compiler failure before verification: exit1,0.81s,153632KiB,swap0.
Exact current error includes:

```text
failed to spawn coordinator thread: Os { code: 11, kind: WouldBlock, message: "Resource temporarily unavailable" }
```

Other concurrent compiler workers fail in rustc_interface/util.rs166 with
`Result::unwrap()` on that same Os11 WouldBlock error. See the complete log,
not only this excerpt. The trivial assertion did not run. The failure is in
compiler fanout, independent of the circle/mask verification property.

The exact invocation is retained in kani-config-002/target.json. It uses the
same cargo-kani0.67.0 and bundled rustc1.93.0-nightly(53732d5e0), original jobs4
and caps. No shared tool/launcher edit or cap increase.

Probe3 will repeat this cold dependency-matched trivial build with taskset
CPU0-3. A reservation refusal at kani-config-003 is uncharged; the fresh
admitted retry will remain the third actual diagnosis probe, not a fourth.


Final diagnosis result: FIXED within3 actual probes.

`kani-config-003-r02`: same dependency-matched trivial harness, cold own
config-target, taskset CPU0-3, original jobs4/TasksMax64/6G/8G/swap0.
Exit0, wall0:19.83, peak RSS533192KiB,swap0; compiler
passes and the arbitrary-u8 identity verifies. Exact argv and all source/lock
hashes are in its target/receipt. The preceding kani-config-003 reservation
refusal was uncharged; it launched no compiler.

Probe count:001 PASS(single crate),002 reproduced compiler Os11/WouldBlock,
003-r02 PASS(cold matched graph with affinity4). No fourth diagnosis probe.
The four-core setting remains confined to this job's command environment.
The failing coordinator/thread-spawn configuration is separate from the
180-second CBMC timeouts of the substantive gates; those are not counted as
compiler configuration failures or checked counterexamples.
