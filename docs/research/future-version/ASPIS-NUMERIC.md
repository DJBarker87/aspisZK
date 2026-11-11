# Aspis failure bound: numeric lemma

Model level. Every figure below is conditional on `FinalDecoding40`, the one
open hypothesis of `AspisFailureBound.Joined.failure_bound40P_of_final`. The
bound has no account term, no payout conjunct and no campaign accounting. It
says nothing about the deployed program. The arithmetic here is compiled; the
figures it gives are not established.

Files: `lean/AspisNumeric.lean` (arithmetic only; imports `AspisRowStarts40`,
`BinCombinedMerkleCollision`, `R0C.SlackBits`, `R0C.SlackObstruction`) and
`lean/AspisNumericBound.lean` (the link to the bound theorem).

## Statements compiled

`rhs Q` is an `abbrev` for the bound theorem's right-hand side, the same term:
`kappa (Q+1111) + ((Q : ℚ) * capMax + verifierCharge40) + 1/2^126 + 1/2^454`.

| Theorem | Meaning |
|---|---|
| `capMax_eq : capMax = UnifiedQueryDensity.queryCap` | the largest class cap is the query cap `C(9557,22)/C(262144,22)` |
| `capMax_le : capMax ≤ 1/2^105` | item 1, upper bound as requested |
| `capMax_le_tight : capMax ≤ 9063/(10000·2^105)` | item 1, upper bound to four figures |
| `capMax_ge : 9061/(10000·2^105) ≤ capMax` | item 1, lower bound to four figures (exact value 0.906199·2^-105 = 2^-105.1421) |
| `classCaps_sum` | the 33 class caps sum to `budget 0 + 25·budget 1 + budget 26 + 4·openingCap + budget 31 + budget 32` |
| `verifierCharge40_closed` | `verifierCharge40 = 1577601·atom + 4·openingCap + 2·queryCap + 34·perElem` |
| `verifierCharge40_le_tight : verifierCharge40 ≤ 15068/(100000·2^100)` | item 2, tighter upper bound |
| `verifierCharge40_le : verifierCharge40 ≤ 151/(1000·2^100)` | item 2 as requested |
| `verifierCharge40_ge : 150/(1000·2^100) ≤ verifierCharge40` | item 2 as requested |
| `rhs_zero_lt : rhs 0 < 151/(1000·2^100)` | item 3 as requested |
| `per_query_core` | the inequality of item 4 for a rational variable `x`, `0 ≤ x ≤ 2^150` |
| `rhs_per_query : Q ≤ 2^150 → rhs Q ≤ (Q+1)/2^100` | item 4 as requested |
| `AspisNumeric.Bound.failure_le_per_query` | item 5: under `hq` and `FinalDecoding40`, failure mass + query-scan failure ≤ `(Q+1)/2^100` for `Q ≤ 2^150`, by `le_trans` of `failure_bound40P_of_final` and `rhs_per_query` |

All targets given in the request held as stated; no constant was adjusted.
The exact values (Python `fractions`, agreeing with the two earlier
computations): `capMax = 0.906199362·2^-105 = 0.966612653·15/2^109`,
`verifierCharge40 = 0.150671834·2^-100`, `rhs 0 = 0.150671849·2^-100`.

Method. The constants are reduced to closed forms by explicit row lemmas
(`budget0_eq` … `budget32_eq`, `sum_range33`) and compared with rationals by
`norm_num`. The query-dependent statement is proved in a rational variable:
`x·capMax ≤ x/2^105`, `x² ≤ 2^150·x` so `6x²/2^256 ≤ 6x/2^106`, the remaining
constants (`verifierCharge40`, `6·1111²/2^256`, `2^-126`, `2^-454`) are below
`2^-100`, and `linarith` combines them. Nothing depending on `Q` is evaluated;
`2^454` is kept as an atom and bounded by `2^-126` (`scan_le`). No `decide`,
`native_decide`, `sorry`, or raised limit.

## Validation

Lean 4.32.0, `fv_lean.sh` on the build host (scope MemoryHigh 6G, MemoryMax 8G,
no swap), against the L187 R1 objects and the Aspis objects in `$W/lean-out`.
Peak RSS includes the memory-mapped imports.

| Attempt | Module | sha256 of source | Exit | Wall | Peak RSS (KiB) | cgroup peak (bytes) |
|---|---|---|---|---|---|---|
| PSN-01 | AspisNumeric | 124f45d9f7c66499ea0dfa3ae39e49c5b804b91e193507c6543b7842b526d0c6 | 1 | 0:29.85 | 7168552 | 3454050304 |
| PSN-02 | PSNTest (scratch, not in the repository) | 7c31607027530e8c8d70478254e7a3b705df13298203e80546a5943f86c7c707 | 0 | 0:02.25 | 4226664 | 432504832 |
| PSN-03 | PSNTest (scratch) | e440d94b269533ccefd5a5d9b6c792cdf82fb5edcb129eaa6797bdee1c34ef06 | 0 | 0:02.48 | 4225656 | 431955968 |
| PSN-04 | PSNTest (scratch) | e3d769ed0dd444348e6c9725781aa8fbb15b199d3715aac02cb5a096e387906b | 0 | 0:02.61 | 4229932 | 433430528 |
| PSN-05 | AspisNumeric | dc2f0d20aaf8d6780a9ec49c9a83cbaafeec1e289648c92a8c72b429dc6318b5 | 0 | 0:03.64 | 4253280 | 449150976 |
| PSN-06 | AspisNumericBound | f977d68d7d32c6c51531900104ccbd002c0996e4d813cddcdf6f48af67b37ebe | 0 | 0:02.14 | 4255460 | 424718336 |

Failed and diagnostic attempts:
- PSN-01: three errors. `classCaps_sum` hit the kernel memory limit (proof by a
  local `List.range 33 = [...] := rfl` rewrite followed by `ring`); `rhs_zero_lt`
  and `per_query_core` failed in `linarith` because `2^454` is above the
  exponent threshold and stayed an unsigned atom.
- PSN-02 to PSN-04: scratch module isolating the `classCaps_sum` failure. The
  written-out sum lemma (`sum_range33`), the row rewrites and a `ring` over
  generalized atoms each check quickly; the final form uses these.
- PSN-05: repairs (sum written out by `List.range_succ`; caps generalized before
  `ring`; `scan_le` bounding `1/2^454` by `1/2^126`). The source compiled is the
  file in the repository.

`#print axioms` for every theorem in both files: `[propext, Classical.choice,
Quot.sound]`.
