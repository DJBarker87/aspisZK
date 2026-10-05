# Wide-field cost screen: results

2026-10-05. Criteria: `PREREGISTRATION.md`, committed in `00b62de78` before
the probe was built. Research only; no verifier, prover, protocol or
parameter of any profile changed.

## Verdict under the pre-registered rules

| Candidate | Floor `F(d)` | Rule | Ceiling `C(d)` | Against 1.4M |
|---|---:|---|---:|---|
| Degree 6, 32 queries | 1,035,381 | **FAIL AT THE 1M CAP** | 5,268,661 | UNDETERMINED |
| Degree 8, 32 queries | 1,036,885 | **FAIL AT THE 1M CAP** | 4,134,581 | UNDETERMINED |

Both floors are above the 1,000,000-CU cap: the extra hashing alone needs
35,381 (degree 6) or 36,885 (degree 8) CU of new savings in the R117 engine,
before any growth in field arithmetic is paid for. Both are below the
1,400,000 Solana maximum, so neither is a HARD FAIL. The ceilings are far
above 1.4M, so the screen does not settle whether either fits one
transaction. That needs a multiplication census of the R117 engine, which is
not in the tree.

This was the outcome stated in advance.

## Kernel costs (M1)

Per operation, `(CU(2n) - CU(n)) / n`, diagnostic cap, five identical runs
each. Every run's final value matched `fields.py`.

| Operation | K4 (QM31) | K6 | K8 | K6/K4 | K8/K4 |
|---|---:|---:|---:|---:|---:|
| Multiplication | 167.0 | 942.4 | 734.4 | **5.64** | **4.40** |
| Multiplication by an M31 scalar | 49.7 | 79.9 | 105.2 | 1.61 | 2.12 |
| Inversion | 785.6 | not measured | 1,482.8 | — | 1.89 |

Rule: as predicted if `r8 <= 3.5` and `r6 <= 2.6`. **Both are worse than
predicted** (`r8 = 4.40`, `r6 = 5.64`).

What this does and does not say. The K6 and K8 kernels are straightforward
Karatsuba compositions of the generic `aspis-core` CM31 and QM31
multiplications (6 CM31 multiplications for K6, 3 QM31 multiplications for
K8). The excess over the operation count (K8: 734 against about 3 × 167 =
501) is overhead of this implementation, most likely array moves between
calls; it was not profiled. The ratios measure these kernels. They are not a
lower bound for a specialised wide kernel. In particular, K6 being slower than
K8 reverses the operation-count ordering and is probably an artefact.

## Authentication with leaf hashing (M2)

Two eight-way depth-six trees, 262,144 synthetic public leaves, one SHA-256
call per opened leaf input and per parent. Whole-program CU, five identical
runs each; corrupted inputs rejected with `Custom(2)` in every run.

| Queries | C2 leaf input bytes | Index set 0 | Index set 1 | `A(q, w)` |
|---:|---:|---:|---:|---:|
| 22 | 220 (degree 4) | 83,639 | 88,104 | 88,104 |
| 32 | 220 | 118,465 | 122,223 | 122,223 |
| 32 | 313 (degree 6) | 119,937 | 123,695 | 123,695 |
| 32 | 406 (degree 8) | 121,441 | 125,199 | 125,199 |

Ten more queries cost 34,119 CU. Widening the C2 leaf costs 1,472 (degree 6)
or 2,976 (degree 8). The query count, not the field width, drives the
authentication increment.

This is authentication only, in a separate program. The R117 verifier's own
authentication cost is part of its 999,790 CU and was not measured here; the
floor assumes the increment carries over.

## Proof size (arithmetic, not measured)

Keeping the 699 fixed fields and widening each to the new field, with the
measured frontier of the larger index set:

| | Fixed fields | 32 records | Frontiers | Total | With a second final array |
|---|---:|---:|---:|---:|---:|
| R102 today (q22) | 11,184 | 13,662 | measured proof 57,682 in total | 57,682 | 61,778 |
| Degree 6, q32 | 16,776 | 22,848 | 46,072 | about 85,700 | about 91,800 |
| Degree 8, q32 | 22,368 | 25,824 | 46,072 | about 94,300 | about 102,500 |

## Deviations from the pre-registration

1. The prebuilt driver's `--micro` flag is unreachable (its argument match
   accepts three arguments only and panics on four). The runs used the
   driver's default mode instead: each fixture at the 1,000,000 and
   100,000,000 caps, honest and with byte 20 flipped. Costs are taken from
   the honest diagnostic-cap rows; the extra rows serve as a negative
   control. The run script was changed accordingly after the first attempt
   panicked; no measurement was taken in the failed attempt.
2. The K4 control is the generic `aspis-core` QM31 multiplication from the
   frozen R101 stage copy, as the pre-registration states.

## Not covered

As listed in `PREREGISTRATION.md`: packed decoding of wider records,
wide-field opening, fold and relation arithmetic, a second final array, and
any soundness or privacy property of either candidate.

## Reproduction and receipts

```sh
cd docs/research/v8-wide-field-screen-20261005
python3 fields.py                       # field construction checks
python3 gen_fixtures.py <new-dir>       # 24 fixtures, expected values included
# upload probe/, run_on_build_host.sh and the fixtures as fixtures/ to the build host, then:
sh run_on_build_host.sh build
sh run_on_build_host.sh run > run.log
```

| Item | Value |
|---|---|
| Probe source `probe/src/lib.rs` | `69ca92315c580c3ac7e09f2bf6bdbbbc9ce0d265855db12b72d83d14890ba689` |
| `probe/Cargo.lock` | `d8b410d98c9b0b1dc6a30509020529046c1cdc825cdcae67505e2309e506fb74` |
| Frozen `aspis-core/src/field.rs` (R101 stage) | `639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499` |
| ELF | `a958cb49ce24a32282657c14ff7d58020fc65966fd0c060564043aa45ae71bd9` |
| LiteSVM driver (R101 stage) | `b6e91ff17ba1f086cc0940ad97accb07108350e6789c82c1f59155f6ff15faa3` |
| Toolchain | platform-tools v1.54, rustc 1.89.0-dev, `opt-level=3`, fat LTO, overflow checks on |
| SBF build | exit 0, 38.64 s, peak RSS 545,896 KiB, 0 swaps, scope 12G/16G, no swap, 128 tasks |
| Runs | 24 fixtures × 5 repetitions × 2 caps × 2 cases = 480 rows; exit 0; 4.03 s; scope 2G/3G, no swap, 64 tasks |
| Determinism | all 96 (fixture, cap, case) groups identical across five runs |
| Negative control | 0 corrupted inputs accepted |
| Fixture generation | local, 0.95 s, 83 MB peak |

`measured-cu.json` holds the status, CU and error of every (fixture, cap,
case) group.
