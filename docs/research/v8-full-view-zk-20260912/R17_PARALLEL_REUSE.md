# R17 parallel opening/group reuse evidence

This note records the already completed R37 opening-reuse and R38 group-dot
offload runs. No run was repeated here. The source base is `020ab456` plus the
staged R17 changes. Both stages retain the same v2 fixture
`d18b5455261d41ba2bbe8d44dd525faa057e50b5110f7cc4225ed32e298204f0`, loaded
from the retained R36 fixture directory.

## Result

The R37 opening stage reaches the primary terminal at **20,479,570 CU**, versus
R36's 20,591,164 CU: **111,594 CU saved**. Its query-schedule-to-openings
interval is **1,622,437 CU**, versus R36's 1,734,031 CU. The R38 group stage
reaches the primary terminal at **20,229,550 CU**, a further **250,020 CU**
improvement over R37's primary checkpoint. Separately, the R38 ordinary-terminal
interval is **1,318,836 CU**, versus R37's **1,568,856 CU** for that same
ordinary-terminal segment.

These are diagnostic primary checkpoints, not complete supported-budget
verifier results. The full honest and mutated runs still fail in the retained
second/reference pass with heap exhaustion; the 1.2M and 1.4M SVM cases fail
the CU meter before primary completion. No privacy, soundness-preservation,
deployment, or security claim follows.

## Resource records

All scopes used zero swap. The declared caps were: host **MemoryHigh=4G,
MemoryMax=6G, TasksMax=128**; SBF **5G/7G, TasksMax=128**; SVM **3G/4G,
TasksMax=64**.

| stage / target | exit | wall | peak RSS | status |
| --- | ---: | ---: | ---: | --- |
| R37 opening host `--gamma-controls` | 0 | 38.16 s | 533,500 KiB | `GAMMA_CONTROLS` passed; canonical, maximal-limb, malformed-input controls retained |
| R37 opening host fixture audit | 0 | 0.03 s | 26,224 KiB | `R17_PUBLIC_PREFIX_ACCEPTED` |
| R37 opening host mutation | 0 | 0.00 s | 3,696 KiB | `R17_LEGACY_PROFILE_REJECTED` |
| R37 SBF build | 0 | 43.05 s | 618,856 KiB | optimized SBF build |
| R37 SVM replay | 0 | 0.13 s | 31,480 KiB | process completed; JSONL records 1.2M/1.4M failures and diagnostic primary marker |
| R38 group host workspace proof | 0 | 55.05 s | 536,048 KiB | 64 carry, 32 terminal, 256 prefix, 32 mask controls passed |
| R38 group fixture audit | 0 | 12.12 s | 449,956 KiB | `R17_PUBLIC_PREFIX_ACCEPTED` |
| R38 group mutation | 0 | 0.00 s | 3,344 KiB | `R17_LEGACY_PROFILE_REJECTED` |
| R38 SBF build | 0 | 40.63 s | 619,840 KiB | optimized SBF build |
| R38 SVM replay | 0 | 0.13 s | 31,752 KiB | process completed; JSONL records 1.2M/1.4M failures and diagnostic primary marker |

## Pins and retained reuse

The R37 and R38 metadata both pin the same opening candidate:

`r17_host_relation.rs` before `ddc3ae6c...5074da`, after
`72597dbb...fab94db`; the retained optimized `query_arithmetic` source and
its canonical controls remain pinned in each `r17-compact-control.json`.
The generated metadata also records the unchanged callback/baseline chain.

The retained helper/proof audit remains the applicable boundary: CircleNorm,
JoinedInverse, LineNorm/LineNormBuffer, QuotientFold, AffinePrimal,
TerminalQuery, InPlaceDenseFold, transported basis/chord work, and the group
workspace controls. Authentication, canonical validation, transcript/query
schedule, both channels, and the independent reference opening remain in the
candidate. No old premise was weakened and no validation was removed.

ELF SHA-256:

- R37: `54c87cc9d169f6a92e71c9f0548e74f67239d9f09e1a969065ccfe06e978545b`
- R38: `52f1b32b5688344c0576841e9702c83b51e1937cf672f07d5f4e5feaad334683`

## Evidence

R37: [host](evidence/r17-parallel-r37-opening-host-r37.log),
[build](evidence/r17-parallel-r37-opening-build-r37.log),
[SVM log](evidence/r17-parallel-r37-opening-svm-r37.log),
[SVM JSONL](evidence/r17-parallel-r37-opening-svm-r37.jsonl),
[probe metadata](evidence/r17-parallel-r37-r17-sbf-probe.json),
[control metadata](evidence/r17-parallel-r37-r17-compact-control.json),
[ELF pin](evidence/r17-parallel-r37-elf.sha256),
[fixture pin](evidence/r17-parallel-r37-fixture-v2.sha256).

R38: [host](evidence/r17-parallel-r38-group-host-r38.log),
[proof](evidence/r17-parallel-r38-group-proof-r38.log),
[build](evidence/r17-parallel-r38-group-build-r38.log),
[SVM log](evidence/r17-parallel-r38-group-svm-r38.log),
[SVM JSONL](evidence/r17-parallel-r38-group-svm-r38.jsonl),
[probe metadata](evidence/r17-parallel-r38-r17-sbf-probe.json),
[control metadata](evidence/r17-parallel-r38-r17-compact-control.json),
[ELF pin](evidence/r17-parallel-r38-elf.sha256),
[fixture pin](evidence/r17-parallel-r38-fixture-v2.sha256).
