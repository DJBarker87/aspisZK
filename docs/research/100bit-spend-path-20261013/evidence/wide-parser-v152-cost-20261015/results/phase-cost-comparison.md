# Phase comparison with prior v1.52 candidate

The two logs share the exact driver (`6510a90ccd2e29989d65be43ba842ad5b95c77b652a4e7eb2f555b8a00285224`), pool/registry, reused proof (`86d4212e675b36ebd556ca2b08b1b5e554cae15e77dfcd74c93a6f419129ed7c`), and public input (`f6bcd49446f1077d2c5ed4be940e91f0be444efc5ae83024ec0700b8c205c331`). Only the selected verifier ELF differs: old `fca47f…`, new `a12e57…`.

The first recorded divergence is at `r1:parsed`: cumulative logged consumption is 54,662 old versus 61,915 new (**+7,253**). It increases to +22,244 at `r1:semantic`, +23,245 at `r1:prepare`, and +24,774 by `r1:query:10`. The matched merkle intervals have equal logged cost; each query interval adds 139 logged units in the new run. These are checkpoint deltas, not attribution to a particular instruction.

| Checkpoint | Old cumulative CU | New cumulative CU | Difference |
|---|---:|---:|---:|
| `parsed` | 54,662 | 61,915 | +7,253 |
| `semantic` | 621,119 | 643,363 | +22,244 |
| `prepare` | 776,492 | 799,737 | +23,245 |
| `merkle:0` | 795,299 | 818,544 | +23,245 |
| `query:0` | 834,129 | 857,513 | +23,384 |
| `merkle:1` | 844,219 | 867,603 | +23,384 |
| `query:1` | 882,982 | 906,505 | +23,523 |
| `merkle:2` | 893,049 | 916,572 | +23,523 |
| `query:2` | 931,709 | 955,371 | +23,662 |
| `merkle:3` | 941,775 | 965,437 | +23,662 |
| `query:3` | 980,430 | 1,004,231 | +23,801 |
| `merkle:4` | 990,492 | 1,014,293 | +23,801 |
| `query:4` | 1,029,135 | 1,053,075 | +23,940 |
| `merkle:5` | 1,039,211 | 1,063,151 | +23,940 |
| `query:5` | 1,077,843 | 1,101,922 | +24,079 |
| `merkle:6` | 1,087,909 | 1,111,988 | +24,079 |
| `query:6` | 1,126,542 | 1,150,760 | +24,218 |
| `merkle:7` | 1,136,595 | 1,160,813 | +24,218 |
| `query:7` | 1,175,247 | 1,199,604 | +24,357 |
| `merkle:8` | 1,185,303 | 1,209,660 | +24,357 |
| `query:8` | 1,223,948 | 1,248,444 | +24,496 |
| `merkle:9` | 1,234,000 | 1,258,496 | +24,496 |
| `query:9` | 1,272,663 | 1,297,298 | +24,635 |
| `merkle:10` | 1,282,731 | 1,307,366 | +24,635 |
| `query:10` | 1,321,385 | 1,346,159 | +24,774 |

The prior candidate passed stage 1: its stage1 log reports 1,389,622 units consumed, while the recorded stage1 execution metric is 1,390,128 CU / 295 bytes. The new candidate failed before `r1:checkpoint-write`; its program log reports 1,399,494 / 1,399,550 units and `ComputationalBudgetExceeded`. Thus no successful stage1 byte count, terminal result, or settlement is available for the new candidate.
