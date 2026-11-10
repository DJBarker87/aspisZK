# PCWU_PATCHES (round 1)

No patch was produced in round 1, so no tool-build scope ran and no TV4 exists.
- Limitation (1): no frozen root reproduces InterpBorrows.ml:2731 under the current pins (PCWU_E001-E003; PCWU_ANALYSIS_1.md). A patch with no frozen reproducer cannot be tested, and upstream would reject it without a test.
- Limitation (2): reproduced (PCWU_E004). The fix needs a new pre-pass (an Option-typed exit local per nested loop, PCWU_ANALYSIS_2.md), written against Charon 454586e9's LLBC types. It is designed but not written. It needs a typecheck environment: the image pcwo-aeneas-pair:t001 has one, but the local opam switch lacks ppx_deriving_hash.
