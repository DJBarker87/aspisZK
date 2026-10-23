# Owned adapter stage 2 — adoption candidate

Branch `codex/cx-adapter-rw-20261023`; base `81521c77f7`. D183, read via
`git show research:docs/research/v8-r0-zk-20261009/LOG.md`, supersedes the
pending domain/error disposition in the stage-1 note. Not merged or adopted.

## Domain and implementation

`AdapterRwRuntimeAdmission.lean` names `RuntimeEntrypointAdmission` separately
from acceptance: fresh live per-account cells, counter0, no external/local
guards, shared cells iff equal keys. Its `Valid` field uses the existing
`S2TrustedSdkBorrow` heap. `runtime-source-check.json` checks SDK entrypoint
2.3.0 creation/duplicate cloning against Agave4.2.1 serialization and duplicate
identification. This is a source inspection supporting a named runtime premise,
not a formal proof of native runtime interpretation. It places no constraint on
adversarial keys, owners, flags, lengths or bytes. Allocation/CU/rollback remain
separate runtime obligations; entry availability is proved without acceptance.

`r1_pool_adapter_owned.rs` replaces both production callers without a feature.
Each selected account has one scoped shared acquisition; no guard crosses any
child call. Metadata are copied too. A single successful exclusive acquisition
copies stage1's returned checkpoint; stage2 writes none. Owned authentication
contains all request, registry, PDA, snapshot, reconstruction and validation
control. Decoder-admitted lengths bound entry allocations. Invalid lengths are
recorded as deferred errors and consumed at their old source positions.

`source-audit.json`: all26 original child/helper bodies remain identical,
including `first_decoded`'s unchanged call path, scanners, emit, checkpoint and
statement children. Existing cone proofs are reused only within their pinned
body/dependency scope; no historical whole-caller/binary proof is reassigned.
The old adapter is retained byte-identically as a cfg(test)-only sibling.
`prepare_owned.py --check` checks the mechanical authentication/caller port.

## Error/effect accounting

No changed error code was observed across1200 distinct mutations and all six
fixtures, both stages. Copy Results are consumed in original source order.
Clock retrieval moves to the wrapper after snapshots; its error is consumed at
the original validation position. Thus rejected malformed request paths may now
perform a clock syscall and bounded snapshots. This is an explicit rejected-path
execution difference, not a discarded digest/query history. Return-data clear
and emit retain their original positions. There are no introduced digest calls.

Raw-SDK nonzero/conflicting counters or unequal keys sharing cells remain outside
D183's domain, not inferred from rejection. Six counter1 diagnostics are labelled
separately. Runtime duplicate entries in the focused differential clone the
first AccountInfo, matching SDK deserialization. Eager allocations can change
resource exhaustion on rejected inputs; source-level unlimited-resource behavior
and measured fixture resource gates are distinct from a universal finite-CU
acceptance theorem. Such a theorem is not claimed by stage2 testing.

## Gates actually run

Host scopes: MemoryHigh6G/MemoryMax8G/Swap0/Tasks64, reservation below55GiB;
optimized Rust and SBF, -j4. Receipt JSON records commands, source/dependency
pins, exits, wall/RSS/swap; keys stay on host, never committed or cleaned up.

Native001:76 tests passed, both adapters' existing tests plus differential.
Native002: focused recheck after correcting duplicate-cell construction; six
transfer/withdrawal fixtures (13/255/1023), both stages,1200 DISTINCT mutated
inputs; exact Result/error, return bytes and full records equal. Fresh counter0
at entry; malformed lengths, tags, metadata, keys and account counts covered.
No unchanged full regression reran.

SBF replay001: all six fixture pairs accepted under BOTH uninstrumented ELFs;
return bytes and checkpoint equal, protected inputs framed, checkpoint metadata
preserved. CU table (stage1 / stage2):

| Fixture | Old CU | Candidate CU |
|---|---|---|
| transfer13 |1208444 /1054799|1210737 /1055602|
| transfer255 |1210550 /1054486|1212843 /1055289|
| transfer1023 |1204676 /1054277|1206969 /1055080|
| withdrawal13 |1204816 /1055626|1207109 /1056429|
| withdrawal255 |1204948 /1054190|1207241 /1054993|
| withdrawal1023 |1206434 /1051815|1208727 /1052618|

Every transaction: +2293 CU stage1, +803 stage2; maximum1212843 CU.
Both12000-increase and1400000-total gates pass.

Heap-build/replay001 uses SEPARATE pinned diagnostic ELFs with identical
terminal cursor logging, no observer change. All six fixtures: old38088/14660
bytes; candidate100032/76644 bytes. Bump deallocation is no-op, so terminal
cursor measures cumulative high water including entrypoint allocation. Both are
below262144 bytes. This is fixture measurement, not a universal heap bound.
Diagnostic CU is not substituted for the uninstrumented release CU above.

## Artifact pins and excluded attempts

Default old `40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0`;
new `d7d42f770883401e0104fb6e044f61a132fea7359943db225d581c5740fcffd0` (1511216 B).
Devnet old `12cb0bc2f8ff3993643638080a3786fdcd941910e5e4dd65ae2937a99290c28f`;
new `2b2a9f0e7a2f93004ddbf207d02f5c5d5155d5c9bfdaeed21a78d638ae9be922` (1511216 B).
Pool old AND new `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`
(605704 B). Pool is unchanged because this work changes verifier caller glue.
Final source inventory builds: sbf004(pool),005(default),006(devnet); final
verifier hashes equal001/002, so the fixture evidence applies to identical ELFs.
The later native-only duplicate-test correction is listed in source-audit.json.

Excluded: rust001 stopped during snapshot (missing tool Cargo.lock; no compiler
run); rust002 failed on historical optional patched-LiteSVM metadata API;
rust003 replaces that optional hook and builds against pinned public API.
Sbf003 refused a stale inventory after test registration;004 updates inventory.
No timeout/OOM, cap increase or unchanged failed retry occurred.

Lean001: runtime premise and3 elementary availability/disjointness theorems,
exit0,0.262197s,763516KiB,swap0; axioms empty or propext. This establishes no
S2CallerFacts field. Stage3 still owes full caller extraction/ports and precise
field-by-field discharge; overall S2/release target not yet established.
