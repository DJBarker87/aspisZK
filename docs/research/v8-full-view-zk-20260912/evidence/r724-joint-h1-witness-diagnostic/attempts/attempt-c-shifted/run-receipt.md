# R724 shifted-z 241-column diagnostic receipt

This standalone Rust source-shaped diagnostic is not an actual selected verifier run, a sampled-prefix result, a privacy proof, or a security conclusion. The shifted parameter tuple is an algebraic witness candidate only; it is not asserted to lie in the selected sampler support.

Source: `src/main.rs`, SHA-256 `fee6f8ca583f27a981c00a5fcdbe8e3cf472af08a14e6702de15714d5fb1a87a`.
Runner: `run-c.sh`, SHA-256 `96134b6b2ad7f65deaff070398e7a0c5627b60b1bda8a1b84ac7d96bded76067`.
Cargo manifest/lock SHA-256: `2ec04695b115df1d4ed6b37d0c713c8193dff02ceb3d0cf90a86527506bb07c8` / `03b8eac78accb5aca38455743db3145f187e638a43ceff56df24692b494b9680`.
Frozen source stage pin: R117 stage `6677d5f1310ff7373301fbd79f186278f772e68a` (source snapshots/hashes are listed under `source-pins/`). Full selected `RUSTFLAGS` file SHA-256: `df02f7fe2415264263ea8dca33d686314b1c06ef27bf4d039df9e587513d28b8`.

The NUC job used systemd user scope `aspis-r724-shifted-c-20261004`, invocation `0871d52f0bfb4f4297ed774fdc7d347c`, with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. The outer shell loaded the complete frozen rustflags file and set `CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true`. Cargo used offline, locked, release, jobs=1, opt-level=3, codegen-units=1. There were no other active Aspis/Lean/Rust scopes immediately before launch; NUC `MemAvailable` was 54,436,860 kB.

Exit statuses: build 0; shifted 23×3 low-constancy preflight 0; shifted 222×241 matrix 0. The preflight reported `all_23x3=true`, 0 differing pairs out of 69, and 0 transport/order mismatches. The matrix rank was 221/222, with 214 core pivots and seven supplemental pivots (columns 214–219 and 228). It emitted the raw 222×241 matrix in four QM31 limbs per entry, row labels, and pair mapping before elimination. The tracked row operations produced a one-vector left nullspace; an independent local check multiplied that vector against all 241 original columns and found zero in each of the four M31 coordinates modulo P. See `pivot-summary.txt`, `left-nullspace.tsv`, `left-nullspace-check.txt`, and full `remote-run/matrix.log`.

Outer time receipt: user CPU 22.87 s, system CPU 0.64 s, elapsed 23.48 s, maximum RSS 595,092 KiB, swap 0, exit 0. `systemd-run` reported service runtime 23.499 s and its displayed memory peak 256.0 KiB; both readings are retained as emitted. Complete build, preflight, matrix logs and status files are in `remote-run/`.

The source formula uses the selected two-swap order, active core pair map, point weights, ordinary relation weights and source-shaped chord transform described in the source and pinned helper snapshots. It does not establish the actual native callback correspondence or the actual adaptive sampled-prefix law. The rank deficiency is an incomplete candidate and is not evidence of a verifier leak.
