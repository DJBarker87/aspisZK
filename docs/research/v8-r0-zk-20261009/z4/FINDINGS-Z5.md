# Z5 — digit-structured transport search

Base: `600eb013878a0169cdab8f222e879cd395e3a1e2` (`origin/v8-reference`).
Branch: `codex/z5-digit-transport-20261010`. Exact M31/QM31 computation only.
Decisions: the final two-transaction/R1 section of the Rust `PLAN.md`, privacy
`LOG.md` D13, and `FINDINGS-C.md`.

**Stage 1 finds three passing digit-position permutations among all 120. The
first pass, `τ=[3,4,2,0,1]` with all σ identity, also passes the full gate:
silent rank 1,076 on every vector, (i′) 100/100, (ii′) 100/100, and empty
excess supports.**
Each passes the C1 rank-112 criterion for all 16 semantic columns on both
fibre sets across all 20 original Z4c challenge vectors. This is a numerical
result on those vectors and fibre sets, not a challenge-uniform theorem.

## Passing transports and search order

Digits are numbered from zero, least significant first. The formula is
`π(r) = Σ[d=0..4] σ_d(digit_τ(d)(r)) · 4^d`.
All five `σ_d` are `[0,1,2,3]` for every pass below.

| Search ordinal (1-based) | τ | Random fibres: ranks 0–15 | Consecutive fibres: ranks 0–15 |
|---:|---|---|---|
| **95** | **`[3,4,2,0,1]`** | 112 each, all 20 vectors | 112 each, all 20 vectors |
| 113 | `[4,2,3,0,1]` | 112 each, all 20 vectors | 112 each, all 20 vectors |
| 119 | `[4,3,2,0,1]` | 112 each, all 20 vectors | 112 each, all 20 vectors |

The selected first pass is therefore

```
π(r) = digit_3(r) + 4·digit_4(r) + 16·digit_2(r)
     + 64·digit_0(r) + 256·digit_1(r).
```

τ is enumerated lexicographically. The planned second stage is lexicographic
`τ × σ_0`; the fallback uses seeded Fisher–Yates per permutation, with
rejection sampling for index selection and a limit of 100,000 draws.
The user confirmed stopping after the first successful exhaustive stage.
Accordingly, all 120 stage-1 candidates were tested, with 3 passes and 117
failures; stages 2 and 3 were not run. Every passing candidate is listed above.
The configured random-search seed is `0x5a35d16120261010`; the Z4c challenge
master seed is `0x5348f0b9a87835d0`. The search seed is used in the separate
cache-audit transport, but no random-search candidates enter the 120 count.

Each candidate is rejected at its first failing challenge, semantic column,
and fibre set (consecutive first within each column). Each pass is checked on
all 20 challenge vectors, 16 columns and both sets: 640 C1 ranks per pass.

## Controls and first failures

Both controls were checked in the same way on all 20 challenge vectors.
Their per-column ranks are constant across those vectors:

| Columns | Identity: random | Identity: `{0,…,21}` | D13: random | D13: `{0,…,21}` |
|---|---:|---:|---:|---:|
| 0–2 | 112 | 80 | 112 | 112 |
| 3–8 | 112 | 81 | 112 | 112 |
| 9 | 112 | 97 | 112 | 112 |
| 10 | 112 | 98 | 112 | 112 |
| 11–15 | 112 | 99 | 112 | 112 |

All 117 rejected candidates first fail at column 0 on the consecutive set in
challenge vector 0. Their first-failure ranks range from 54 to 111. The exact
histogram is in `summary-Z5.json` (`first_failure_rank_distribution`); this is
a histogram of the first rejected column, not a claim that every later
column/challenge was evaluated after rejection.

For the first 20 failures, the table gives that first failing column's rank.
`summary-Z5.json` and `probe-Z5.log` additionally report all 16 per-column
ranks on both sets for each of these candidates. Every σ is identity.

| Ordinal | τ | Column 0, consecutive |
|---:|---|---:|
| 1 | `[0, 1, 2, 3, 4]` | 80 |
| 2 | `[0, 1, 2, 4, 3]` | 70 |
| 3 | `[0, 1, 3, 2, 4]` | 66 |
| 4 | `[0, 1, 3, 4, 2]` | 56 |
| 5 | `[0, 1, 4, 2, 3]` | 56 |
| 6 | `[0, 1, 4, 3, 2]` | 56 |
| 7 | `[0, 2, 1, 3, 4]` | 82 |
| 8 | `[0, 2, 1, 4, 3]` | 76 |
| 9 | `[0, 2, 3, 1, 4]` | 86 |
| 10 | `[0, 2, 3, 4, 1]` | 92 |
| 11 | `[0, 2, 4, 1, 3]` | 80 |
| 12 | `[0, 2, 4, 3, 1]` | 92 |
| 13 | `[0, 3, 1, 2, 4]` | 68 |
| 14 | `[0, 3, 1, 4, 2]` | 62 |
| 15 | `[0, 3, 2, 1, 4]` | 82 |
| 16 | `[0, 3, 2, 4, 1]` | 92 |
| 17 | `[0, 3, 4, 1, 2]` | 73 |
| 18 | `[0, 3, 4, 2, 1]` | 89 |
| 19 | `[0, 4, 1, 2, 3]` | 58 |
| 20 | `[0, 4, 1, 3, 2]` | 58 |

## Observation map and computational scope

The matrix is exactly Z4c's C1 matrix: four QM31 claims (16 M31 coordinates),
two QM31 OOD values (8 coordinates), and 88 opened M31 symbols. Its sources
are the same eligible semantic rows, balanced against row 1023 when inactive.
Balance is a source constraint; the observation dimension is 112.

The search caches row-indexed point-claim weights separately from
coefficient-indexed Libra, OOD and opened-symbol weights. Semantic columns
with identical eligible-row lists share a computed rank. The six source-list
groups are `[0,0,1,2,2,2,2,2,2,3,4,5,5,5,5,5]`. Elimination can stop when all
112 pivots exist. The cache preflight compares every one of the 1,024 balanced
row vectors and every column rank with the original uncached C1 loop, on both
sets, for identity, D13 and a seeded digit transport.

The existing `Ech`, circuit, `lane_eliminate`, `pure_c`, `full_c` and `gate_c`
routines are byte-for-byte unchanged from the base. No new rank machinery is
introduced. Only research sources in `z4/` change.

For the selected transport, every opening/OOD coefficient lookup, fourth-row
weight and Libra monomial lookup uses its π. Eligible padding sources remain
row-indexed and their coefficient positions are their actual images under π;
there is no assumption that the first 89 coefficients are pads. The probe
prints those images for each column. The inverse permutation, actual
`eval_message` identity, and all 56 Libra monomials through all ten rounds at
four evaluation points pass the focused preflight.

The full-gate experiment is Z4c's width-29 generic gate: twenty challenge
vectors, ten genuine same-statement witnesses in five pairs, and five noise
tapes per vector. γ=7 and the simultaneous zero-batched-word lifts are
unchanged. The derivative-subtracted target is a diagnostic; the main target
retains D12's full remainder. No Lean, production Rust, or probability ledger
is changed.

## Full gate result

| Selected transport | Challenge vectors | Silent rank | Initial retained rank | Full conditioned rank | (i′) | (ii′) | Derivative diagnostic | Excess |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| `[3,4,2,0,1]`, all σ identity | 20 | 1,076 each | 1,080 each | 1,080 each | 100/100 | 100/100 | 100/100 | 0; supports and pivots `[]` |

All 20 complete challenge records and all 100 pre-normalization terminal
diagnostics match `probe-C.log` exactly. The full gate independently reports
112 for every semantic-column C1 rank on both sets in every vector. All 60
result records (i′, ii′, derivative) have zero failures and zero excess.

As in Z4c, the simultaneous zero-batched-word construction gives a subspace
of the silent image. Its observed rank reaches the 1,076 boundary/terminal
upper bound in each generic vector. The evidence is finite-field computation;
it does not discharge a Lean containment theorem or establish the property
for all challenge/fibre choices. No runtime cost or R1 fit claim follows from
this report alone.

## Resource and source evidence

Every attempt ran in its own user systemd scope with `MemoryHigh=3G`,
`MemoryMax=4G`, and `MemorySwapMax=0`. Initial populated finite caps were
24.375 GiB; this probe reserved another 4 GiB, below the 55 GiB safe limit.
The isolated Cargo release profile has `opt-level=3` and overflow checks.
Heavy arithmetic time is spent in the original terminal-polynomial evaluation
and conditioned elimination; no debug binary performed the gate.

| Attempt / target | Exit | Wall seconds | Peak child RSS KiB | Cgroup peak bytes | Swap peak bytes |
|---|---:|---:|---:|---:|---:|
| `preflight/compile` | 101 | 0.019 | 20,768 | 20,082,688 | 0 |
| `preflight2/compile` | 101 | 3.475 | 277,940 | 316,858,368 | 0 |
| `preflight3/compile` | 0 | 47.129 | 547,552 | 856,055,808 | 0 |
| `preflight3/probe` | 0 | 0.420 | 18,128 | 856,055,808 | 0 |
| `search/compile` | 0 | 5.301 | 268,720 | 183,730,176 | 0 |
| `search/probe` | 0 | 3.919 | 26,180 | 183,730,176 | 0 |
| `gate-preflight/compile` | 0 | 5.161 | 268,820 | 184,184,832 | 0 |
| `gate-preflight/probe` | 0 | 0.029 | 18,304 | 184,184,832 | 0 |
| `gate/compile` | 0 | 0.033 | 28,856 | 24,760,320 | 0 |
| `gate/probe` | 0 | 1235.503 | 39,704 | 54,317,056 | 0 |

Cgroup peaks are cumulative within a scope, so a preflight probe inherits its
compile peak. The full arithmetic gate took 1,235.503 seconds, with peak child
RSS 39,704 KiB (38.77 MiB), cgroup peak 54,317,056 bytes (51.80 MiB), and swap
zero. At the ten-minute review, 50 targets had passed, memory-pressure and OOM
counters were zero, and a vector completed about every 61 seconds. The gate
continued under the original caps; no cap was raised.

Two setup failures are preserved. The first staging pass omitted Cargo's
explicitly declared example files; the second omitted `aspis-core/build.rs`,
so `OUT_DIR` and generated circle tables were unavailable. Both were repaired
by copying unchanged files from the pinned base. `build.rs` was added to the
source manifest, and the fallback seed literal was corrected to its intended
64-bit value before the successful build. The exact failed receipts, source
hashes and compiler logs remain under `z5-attempts/` and in the evidence index.

The source audit verifies all **203 compiled-source hashes**, seven decision
and audit-source hashes, and byte identity of the six existing elimination
routine blocks. `rustc 1.94.1 (e408947bf 2026-03-25)` built the locked release
profile. Successful dependent steps reused its cache. Exact source snapshots
and build logs remain on the host at
`/home/dombarker/project-offloads/aspis-z5-20261010/`.

Artifacts: [evidence-Z5.json](evidence-Z5.json),
[summary-Z5.json](summary-Z5.json), [probe-Z5.log](probe-Z5.log),
[z5.rs](z5.rs), [run-z5.py](run-z5.py), and
[summarize-z5.py](summarize-z5.py). The summary contains every passing
candidate, per-vector/per-column ranks, full first-20 failure records, the
failure histogram, controls, and every full-gate excess support.

Reproduce on the dedicated Linux host from this branch:

```sh
systemd-run --user --scope --unit=aspis-z5-search-reproduce \
  -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 \
  python3 docs/research/v8-r0-zk-20261009/z4/run-z5.py \
  --out /tmp/aspis-z5-search-reproduce

systemd-run --user --scope --unit=aspis-z5-gate-reproduce \
  -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 \
  python3 docs/research/v8-r0-zk-20261009/z4/run-z5.py \
  --out /tmp/aspis-z5-gate-reproduce --mode gate \
  --candidate /tmp/aspis-z5-search-reproduce/first-candidate.txt
```

Audit the committed evidence with
`python3 docs/research/v8-r0-zk-20261009/z4/summarize-z5.py`.
No Lean was run; neither Lean nor production Rust was edited. No binary or
co-author trailer is included. `#print axioms` is not applicable.
