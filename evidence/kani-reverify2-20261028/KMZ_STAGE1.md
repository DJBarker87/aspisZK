# Stage 1: confirmed-row controls

All five rows: **CONTROLS FAILED AS REQUIRED (credit stands)**. No CONTROL PASSED.

| Row | Negative controls | Concrete witness replay |
|---|---|---|
| LPn_K001 | K002 for KMY_K006 | R001 |
| LPa_K015 | K003 for KMY_K018 | R002 |
| LPb_K016 | K004/K005; K007/K008/K029/K010/K030–K031/K012; K027 | R003, R004 for shared limb gate |
| LPe_K005 | Same shared serializer/six-stage controls as LPb_K016 | Same shared replays |
| LPe_K019 | K006; K013–K026 (14 distinct stages); K028 | R005 |

Numbers in this table use the KMZ_ prefix. Every credited control has exactly one failed check, the deliberately changed byte equality or capacity expectation. KMY_K007 (zero fill), K008 (metadata), K072 (indexed decoder), K073 (decoder boundary) contain no KMX copy-dependent window requiring another copy control. Their existing positive evidence is retained.

K011 really timed out with no counterexample and earns no credit. K030/K031 replace it with the prefix and appended windows of stage4; their selected-byte domains partition the original assertion. They retain its allocator/copy stubs, canonical inputs, unwind258, optimized profile, and successful allocation scope. These two windows failed the wrong-byte assertions. K012 completed with a solver-generated concrete playback; it was not rerun.

K001: own literal `$` harness filter selected nothing; corrected with a unique selected function name. K009: own missing `-Z concrete-playback`; corrected in K029. Reporting trace/playback options were subsequently removed because they made counterexample reporting expensive. This does not change the checked semantics. All three attempts are retained and counted. The wrapper initially misclassified K030/K031 by matching `--harness-timeout` in a printed command; KMZ_audit.py corrected their classifications from actual verification summaries (29.96s/31.96s). No proof was rerun to repair that label.

Concrete witnesses: all-zero arbitrary prefixes and sources; canonical WideExact zero, arbitrary-bit QM31 zero, offset0, selected local byte0 (global128 for stage4's appended window). The asserted XOR1 byte is 1 while the correct value is 0; equivalently the expected byte is changed by XOR1. Native R001–R005 check the correct relation and the deliberate mismatch, with the exact unchanged KMX definitions. R003 includes all six heap stages and capacity32; R005 includes all14 scalar stages and capacity16. Native allocator internals are native, so these corroborate concrete witnesses rather than replace the stubbed Kani heap proofs. K029/K010/K012 additionally retain solver-produced playback values in stdout. The native replay source specifies both prefix and appended local-byte-zero witnesses.

Patch SHA-256: bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
Stub-file SHA-256: c282a1272676cd56fd2702f60b17009bac9d252e495b1508459b01d6ed1cf9d9.
Frozen lock SHA-256: 5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef; independently matched against `git show 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:Cargo.lock`. Reused KMY_src is the existing scratch crate with that copied frozen lock, not a second corpus/workspace.

Stage1 accounting: Kani31/70 =28 failing controls, one timeout, two own option/filter errors. Rust5/5 optimized witness runs. Lean0/60. All admitted scopes satisfy6G/8G/no swap/64 tasks. Graphs validated before every Kani/native invocation; lock hashes unchanged afterwards. Full per-attempt statuses, timing, RSS, swap, revisions and hashes: KMZ_RUNS.json and individual receipt.json files. No original-property counterexample occurred.
