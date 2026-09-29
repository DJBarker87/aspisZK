# R54 preflight and resource record

Base: `eaa0435c1e71b9605af40daf7b07cefd3bcb5e92` (pushed R53).
All remote execution used Tailscale `100.108.41.90`. Preflight found 62 GiB
RAM, 47 GiB available, and only the user init scope running. Existing system
swap was 7.5 GiB; every new scope forbade swap.

Focused Lean jobs reused R53's 279-object source-aware cache, advancing
through R54 stages a–i. Each scope had MemoryHigh=3G, MemoryMax=5G,
MemorySwapMax=0, TasksMax=128. Two missing unchanged circle algebra leaves
were compiled explicitly; no package-wide or cold dependency build ran.
No expensive finite-support enumeration was used by the executable exporter.

Rust compilation/replay used MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0,
TasksMax=128, with --release --locked --offline --jobs 2 and overflow checks.
Compilation was the expected expensive phase; no dense elimination ran.
Jobs were serial, so maximum simultaneous reservation was 7 GiB.

Retained focused failures: b (conditional branch simplification), c (missing
unchanged ExactTowerChord dependency), d (circle projection names, explicit
Option conversion and field denominator normalization), e (ambiguous name),
f/g (residual inverse-of-two normalization), h (reserved `prefix` identifier
in the exporter). Changes or the specifically missing dependency preceded
each rerun. Limits were not raised. Successful final leaves are a, c, g, h,
and i. Failed audit output with sorryAx is not counted as a successful proof.

The source control manifest has 197 entries; the test stage adds only the
new replay target and its Cargo declaration. Production verifier/transcript
and circle code are unchanged. No new SBF/CU execution was justified.
