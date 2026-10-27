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
