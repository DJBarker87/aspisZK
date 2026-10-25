# Exact captured resource denial: retain policy, no admission patch

Reviewed offline on 2026-10-25. Entry source revision:
`49f36dfb1b2b3a1ee93c21b847757462f477caed`.
Read repository AGENTS.md and the linked local Linux HANDOFF.md, including its
strict55/reserve7/guard2, both-scan and count-own-cap-once requirements.
No launcher, admission, frozen source, contract, target or trust premise changed.

## Arithmetic and decision

Both captured snapshots completed, membership differences=0. The external
15,473,168-byte stdout SHA256 is
`279909c5bbd0a7c1f281d6bf217de8b59a85ed6c8ec0f9f14ee24d568977bd94`.
Its hash/size and the compact actual-publication-result.json agree with this review.
No large derived JSON was copied into the repository.

All values below are GiB (2^30 bytes):

| Quantity | GiB |
| --- | ---: |
| Minimum MemAvailable | 51.981098175 |
| Maximum active file deduction | 9.484371185 |
| Maximum kernel withheld deduction | 6.377773285 |
| Maximum full root residual deduction | 2.122047424 |
| Adjusted availability | 33.996906281 |
| Existing finite frontier caps | 24.375 |
| New independent cap | 8 |
| OS/control reserve | 7 |
| Required | 39.375 |
| Deficit | 5.378093719 |

Exact bytes: 55,814,279,168 - 10,183,766,016 - 6,848,081,920
- 2,278,531,072 = 36,503,900,160; required = 26,172,456,960
+ 8,589,934,592 + 7,516,192,768 = 42,278,584,320.
The strict inequality fails by 5,774,684,160 bytes. Cap<55 GiB, available>
request+2 GiB and legacy nonreserve gates all pass. The historical pinned Port17
admission checks only frontier+8<55, hence passes at 32.375 GiB. It does not
establish the newer adjusted-memory bound.

## Safety interpretation

This is deliberately conservative accounting, not evidence of physical inability
to run Lean and not an identified unsafe bound. MemAvailable already reflects
occupied/unavailable memory and estimates reclaimability; charging full caps
again can overlap present usage. Active file, withheld kernel and root residual
can also overlap accounting categories. The evaluator explicitly requires these
extra deductions, rather than claiming a disjoint physical-memory partition.
Its denial is therefore a policy result, not a capacity theorem. Passing it
would likewise not guarantee capacity against arbitrary uncapped future growth.

There is no justified small correction established by these captures that both
retains the required policy and admits this request. The finite frontier is
already counted once. Prospective request=8 GiB; inside-scope request=0 prevents
charging the new scope twice. Neither adjustment fixes this outside-scope denial.

Subtracting all frontier current usage from reservations is unsafe: current
reclaimable pages may already contribute to MemAvailable. Toy counterexample:
30 GiB total, capped current=cap=20 GiB entirely reclaimable inactive file,
uncapped nonreclaimable current=10 GiB, MemAvailable=19 GiB, active/kernel/root
extra deductions=0. Remaining-cap arithmetic asks only for new8+reserve7=15,
passes guard2 and cap55, yet full caps28+uncapped10=38 exceed physical30 even
before reserve7. Reclamation cannot both fund the new allocation and preserve
the old full reservation without additional capacity.

Replacing available with total also needs bounds on uncapped current AND growth.
Toy counterexample: total64, capped cap24/current1, uncapped nonreclaimable40,
root residual2, active/kernel deductions0. Total-based test sees 64>24+8+7+2=41,
but simultaneous required capacity is 24+8+40+2+7=81. Both scans can have identical
membership and these usages. They do not establish zero future service/VM growth.
In the real capture, total=62.117970 GiB; accounted current outside the finite
frontier is 49.062416/49.068779 GiB. Those totals include reclaimable memory;
treating them all as permanently unavailable is also unjustified. No disjoint
reclaimability or enforced future-growth bound has been established here.

## Smallest concrete next action

Keep the existing policy and 6G High/8G Max/Swap0/Tasks64 route. Wait for already
capped work to finish normally and release enough reservation, then let the
manager authorize fresh admission under unchanged controls. At otherwise fixed
metrics, reservation reduction must exceed 5,774,684,160 bytes: 6 GiB suffices,
5 GiB does not. This is a conditional numeric requirement, not a guarantee that
completion will leave MemAvailable and deductions unchanged. No service/VM
termination, host action, allocation or retry is authorized by this report.
Alternatively any accounting-policy redesign requires a separately justified
bound and explicit owner decision; no speculative relaxation is prepared.

Before/after policy is identical: all visibility and both scans, full residual,
strict55, reserve7, guard2, separate scope controls, count-own-cap-once and no
unchanged OOM cap raise remain required. Soundness367/368 and privacy finalKani59/60
remain reserved. Both deployed targets are NOT ESTABLISHED. No proof claims.

## Reproduction, pins and measured validation

Exact validation command (exit0):

```
python3 evidence/port36transport-20261025/linux367/numeric-denial-review/review.py
```

The committed script only reads captured/local files and two immutable git blobs.
`result.json` records their source pins, SHA256/size, scalar pass/fail boundaries,
original receipt agreement and per-snapshot current summaries. These are arithmetic
checks, not a full evaluator replay, new snapshot validation or admission authority.
Evaluator reviewed at `f7b90c82300c8a2409625fefb5dc529db6547f9c`;
Port17 reviewed at entry `49f36dfb1b`; local candidate observe() is source-hashed.
Validation wall=0.1071442081592977 s; peak self RSS=77,611,008 B;
peak serial child RSS=6,012,928 B; both ru_nswap counters=0 (swap bytes unobserved).
`#print axioms`: N/A, no Lean invoked. Preliminary source-read commands exited0;
one glob had no matches and one rg named an absent local directory; neither
was an evidence or policy test. Their RSS/swap were not instrumented.

Only local source inspection, captured JSON parsing, hashing, arithmetic and git
were used. No host/SSH/query/transfer/scope/compiler/backend/native action occurred.
The existing denial is retained without a launch or cap change.
