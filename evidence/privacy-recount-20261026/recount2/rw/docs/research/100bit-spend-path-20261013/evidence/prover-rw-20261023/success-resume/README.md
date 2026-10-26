# Stage 3 resume evidence

This is an unmerged prover candidate. The deployed real-prover refinement,
conjunct 1 of `ProverCommitDeployedFuel22.RustProverRefinement`, remains open.
Root/headline premises removed: **0**. No security target was reduced.

- `final-state.json`: source hash validation, interpretation classifications,
  exact remaining successful-body reference IDs, root hashes and open obligations.
- `summary.json`: all 85 focused Lean attempts 12416–12500, 46 pass/39 fail.
- `<id>-receipt.json`: exact target/command, source revision/hash, dependency
  fingerprint, limits, exit, wall time, RSS, swaps, full axioms and errors.
- `<id>-input.json`, `<id>.lean.txt`, `out-<id>.log`, `time-<id>.log`:
  immutable captured inputs, source snapshots and raw successful/failed output.
- `audit-targets.json` and attempt12500: one combined audit of129 new theorem
  declarations, standard axioms only. Exit0, wall1.76s, RSS4288784KiB, swaps0.
- `native/summary.json`: all11 Kani invocations,6 pass/4 timeout/1 compile
  rejection. Explicit destructor-cut limitations remain; this does not prove E1.
- `*-source.json`: retained-source generator pins. All relevant --check runs pass.
- `history-through-proof-checkpoint.txt`: requested branch history through the
  last proof-source commit, before this final evidence-only checkpoint.

The existing stricter Lean launcher uses5G/7G/swap0/Tasks64 and -M7000.
Native scopes use6G/8G/swap0/Tasks64, optimized profile3 and j4.
No caps, launcher or infrastructure changed. There was no OOM or swap.
The heartbeat-limited monolithic wide proof was split; failed source inputs
were changed. No exact source+dependency fingerprint is repeated. An early
source receipt was reconstructed, with its actual empty launcher argument
recorded explicitly; this was a single launch. Local/pre-launch preparation
errors are identified separately from proof runs. The vanished-cgroup retry
exception was not needed during this continuation.

No release/full manifest or runtime/ELF rebuild was run. Production Rust bytes,
release pins and the security root are unchanged. The sole Rust change extends
an existing cfg(kani) module; its inherited prefix is verified unchanged.
The native source/artifact association remains an open adoption obligation.

Read-only regeneration of receipt summaries and validation:

```sh
python3 tools/prover-rw-20261023/success-install/collect-resume.py
python3 tools/prover-rw-20261023/success-install/native-resume-report.py
python3 tools/prover-rw-20261023/success-install/final-resume-report.py
```

These scripts do not launch a build. No binaries or compiled caches are retained.
