This is the actual saved-S2 differential kit for Decision 1d and the Decision
1f fixed-ten semantic-round unroll. It reads the complete baseline
`verify_observed` from `deb68369b`, and the complete final `verify_observed`
and `verify_finish` from the explicit `--after` Git revision. The source
candidate is never edited. `--stage` accepts only a separate, clean snapshot
whose semantic source is byte-identical to that Git revision.

```sh
python3 tools/r1-verify-migration-kit/prepare.py --after FINAL_REV
python3 tools/r1-verify-migration-kit/prepare.py --after FINAL_REV --check --stage ISOLATED_SOURCE
```

The test-only overlay appends the complete baseline function under a different
name and symmetrically replaces five kinds of child calls with wrappers.
Each successful wrapper calls the actual production implementation. The
wrappers inject explicit synthetic errors at parse, public-transcript and
begin entry, and at both record lookups, polynomial decoding and semantic
sampling for every row 15..24. A separate coefficient perturbation exercises
the original boundary check and its original error branch at each round.
The moved row-14 initializer also gets lookup and decode failures.
These configured failures are not asserted reachable on a valid production
input. All transformation counts and complete source/overlay hashes are in
`source-pins.json`.

There are 55 failures and one success control, each with `Some(observer)` and
`None`: 112 cases per binary. Run two focused native builds, with and without
`detail-phases`, for 224 cases total. Each compares the complete returned
semantic data, transcript state and row, actual SHA digest slice inputs and
answers, native trace values, interface-call events and observer phases.
Failure observations must also be prefixes of the successful run. The
fixture uses the real fields, parser, transcript, polynomial folds and
terminal evaluation. It does not generate another proof. The semantic
verifier has no variant argument; this does not claim valid S1/D proof
execution.

In the dedicated build host, use the existing pinned optimized native
workspace and its runner. Each job needs MemoryHigh=6G, MemoryMax=8G and
MemorySwapMax=0, plus the aggregate-reservation preflight. The two commands
are the following (the pinned optimized equivalent profile is also valid):

```sh
cargo test --release --locked --offline -j1 -p aspis-r1-cost-probe --features prover,private-leaf-salts,optimized-terminal --lib r1_semantic::verify_migration_tests::verify_saved_s2_exact_old_new_all_round_failures_and_success -- --nocapture --test-threads=1
cargo test --release --locked --offline -j1 -p aspis-r1-cost-probe --features prover,private-leaf-salts,optimized-terminal,detail-phases --lib r1_semantic::verify_migration_tests::verify_saved_s2_exact_old_new_all_round_failures_and_success -- --nocapture --test-threads=1
```

Require all per-case lines and `VERIFY_REAL_S2_PASS cases=112` in each log.
Retain exact command, exit, wall time, peak RSS, swap and source/overlay pins.
`#print axioms` is N/A for this Rust gate. No SBF, Lean, readonly runtime
harness or live-worktree mutation is part of this kit.
