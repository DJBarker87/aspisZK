# R724 shifted-z 242-column missing-direction diagnostic

This is a standalone Rust, source-shaped linear algebra diagnostic. The shifted tuple only supplies algebraic chord parameters; its CM31-subfield inputs are rejected by the selected OOD sampler. It is not asserted to be an accepted OOD sampler prefix and is not a native verifier run, privacy proof, or security conclusion.

Source `src/main.rs` SHA-256: `bf81087c0a18686ea282b38ed87088cf0b998f0f47e4a5bd124ea8905adacb1f`.
Exact changed-source diff from reviewed C SHA-256: `7fafc6e02f83f641bf7c291c638b5b4eac92414250763a9b596ce697cbef114a`.
Runner `run-d.sh` SHA-256: `2a8d375e0545f3972200df8d5f543d9877a4e1327188ec7b76b73771d4147b25`.
Cargo.toml/Cargo.lock SHA-256: `2ec04695b115df1d4ed6b37d0c713c8193dff02ceb3d0cf90a86527506bb07c8` / `03b8eac78accb5aca38455743db3145f187e638a43ceff56df24692b494b9680`.

Compared to the reviewed C source, this adds exactly one supplemental input direction `(47,3)` after asserting the pair is absent. The shifted parameter tuple, 214 core columns, original 27 supplemental columns, matrix rows, formulas, and elimination remain unchanged.

NUC unit `aspis-r724-single-column-d-20261004.service`, invocation `fe0dc42228f74d13a72c6be220d2e205`; cgroup `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`. Before launch no Aspis/Lean/Rust service was running and `MemAvailable` was 54,686,728 kB. Full R117 frozen RUSTFLAGS SHA-256 `df02f7fe2415264263ea8dca33d686314b1c06ef27bf4d039df9e587513d28b8` were loaded by the outer shell and overflow checks enabled. Cargo used offline/locked/release/jobs=1, opt-level=3, codegen-units=1.

Exit statuses: build 0; shifted 23×3 low-constancy preflight 0; matrix 0. The preflight reported zero differing pairs out of 69 and zero transport/order mismatches. Matrix size 222×242, rank 222, 214 core pivots, 8 supplemental pivots; complete pivot and pair lists are in `pivot-summary.txt`. The complete original matrix is in `remote-run/attempt-d-shifted/matrix.raw.tsv` as four QM31 limbs per element before elimination.

The independently-run check `check_d_against_c.py` compares every one of the 241 C columns against the corresponding D entry across all 222 rows; they match exactly. It then evaluates the prior C left-null vector against the new column and obtains `(1909084209,0,0,0)` mod P, matching the independent exact chord-transpose omitted-pair computation. The check script and its output are saved next to this receipt.

Outer time receipt: user CPU 22.74 s, system CPU 0.62 s, elapsed 23.34 s, max RSS 597,924 KiB, swap 0, exit 0. systemd reported service runtime 23.348 s, CPU 23.378 s, memory peak 328.0 KiB and swap peak 0 B; both metrics are retained as emitted in `systemd-terminal.txt`.

The matrix’s 222 rows are 214 selected active chord observations, three point observations, and five ordinary relation coefficients. It does not include the 88 actual query-root observations. Its construction checks the prior low-23 constant-observation shortcut, first-fold zero, four high-tail zeros, inactive balance, and a 23×3 same-slot low-observation constancy preflight. This run did not separately compare all 214 core observations before and after the low correction; that remains a source-shape/formal boundary. The formal augmented-23-root section (the 22 selected query roots plus root 1, with the noncollision condition from R691) remains open, as do a formal joint-minor proof, actual legal-prefix justification, causal shared-oracle accounting, simulator construction, and probability-loss accounting. This full-rank result is only a field-model witness search at an algebraic, unsampled tuple; it is not a full privacy result.
