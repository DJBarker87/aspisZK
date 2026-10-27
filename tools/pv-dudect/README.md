# V374 candidate-kernel preparation

This standalone, unpublished host binary is outside the root workspace and
outside every release build. It is synthetic diagnostic software. It creates
no wallet, account, reservation, transaction, or proof. No kernel source is
maintained here. `#[path]` links the private cost-probe leaves directly;
`source-link` token-includes complete candidate prover modules from `crates/`
and appends access adapters in their scope. It strips only inner doc comments.
It neither edits function visibility/bodies nor substitutes entropy/hash stubs.
Core arithmetic is linked through the actual `aspis-core` dependency with
`ct-host-prover`. Hashing uses `aspis_prover::HOST_HASH`.

The private-source adapters are new compilation contexts. **Source identity
is not instruction identity.** See the committed symbol comparison and plan
before attributing any result to `devnet_spend`. A seed-check result measures
`entropy_nonzero32`, not the OS call, caller's short circuit, full entropy retry
loop, or the complete account route. The inverse experiment excludes zero;
zero inversion/panics are not mixed into the nonzero experiment.

The deterministic public experiment seed is `0x563337342d763200`; SplitMix64 is
only a reproducible synthetic input/order generator, not cryptographic entropy.
Fixed seeds are `[0x35;32]`. No live secrets are accepted or exported. Allocating,
shuffling, randomizing inputs, expander initialization and zeroizing drops occur
outside intervals. Every call result reaches `black_box`; result status is
counted after the ending counter. Public dispatch precedes the initial counter.
Counter intervals contain LFENCE/RDTSCP/LFENCE at both ends, compiler fences,
and a kernel call or its actual inlined code; cycle overhead is not subtracted.
All experiments are single-threaded and pinned to logical CPU 2.

Commands (host, separate admitted 6G/8G/swap0/Tasks64 scopes):

```
RUSTFLAGS='-C link-arg=-Wl,--threads=4' cargo build --manifest-path tools/pv-dudect/Cargo.toml --release --offline --locked -j 4
taskset -c 2 /home/dombarker/project-offloads/codex-pv-dudect-20261027/bin/pv-dudect --dry-run 1000
```

`--dry-run` refuses any existing quiet marker, runs only 1000/class, emits cost
summaries labelled **not a measurement**, writes no raw timing files and runs
no significance test. `--measure` requires a currently active marker, accepts
only the preregistered count 1,000,000/class, warms up with 10,000 untimed calls
per family, and writes exclusive-create CSVs with cycles, class, CPU IDs,
validity and result status. Migration aborts after retaining the family; no
resampling occurs. `window_worker.py` adds live competing-job/cap/deadline
checks. `analyze.py DIRECTORY` performs the preregistered offline analysis.

The future **lead-only** command is in `V374-PLAN-v2.md`. Neither this package
nor any preparation command creates, modifies or deletes `QUIET_WINDOW.json`.
DOITM stays OFF (V371). No timing result establishes constant time or privacy.

The separate `src/bin/diagnostic.rs` binary implements the D295 artifact
controls: **diagnostic, not a V374 measurement**. It refuses an existing quiet
marker, pregenerates all inputs, copies every class through a common fresh
buffer and interleaves six balanced pairs in one run. Build it with
`cargo build --release --offline --locked -j 4 --bin diagnostic` under the
normal admitted caps. `diagnose.py build|controls|analysis|trace` launches
sequential task-local scopes and requires both exit 0 and `allowed:true` from
admission. It never requests or writes a quiet marker. This does not change
the original `--measure` preregistration. See `dudect/DIAGNOSIS.md` in the evidence.
