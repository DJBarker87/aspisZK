# NER coherent replay completed, 2026-11-03

All **1,387 required model modules compile unchanged** against the headline
cohort. The three stale modules and two intermediate modules were already
rebuilt in R020-R024; this continuation rebuilt 1,381 ordinary modules in
37 batches and NDR_CombinedAudit once in A900. No theorem failed against the
current definitions. No model, protocol source or theorem statement was edited.

NER_REBUILD_ROWS.jsonl contains every rebuilt source/object hash, selected
direct-import hashes and receipt reference. NER_rebuild_checks.py validates all
1,387 pairs, requires each affected import to equal its final rebuilt object,
and rejects a planted stale-import hash. The unchanged upstream cohort is
reused with its original object/private pins. Per-batch module lists, exits,
wall time, RSS, swap, source revision and caps are in NER_BATCH_SUMMARY.json;
per-module commands, measurements and actual #print output are in each
NER_Bxxx-details/modules.jsonl and its logs. Sources without a print command
are not claimed to have a separate print query; both release roots are queried
and independently raw-walked in the final audit.

The maximum batch process RSS was 7,214,216 KiB;
every batch exited 0 and reported zero swaps. All used MemoryHigh 6G,
MemoryMax 8G, MemorySwapMax 0, TasksMax 64, -M7000, -j1 and async elaboration
disabled. At most two scopes and one Lean process per scope ran concurrently.
Five refused quiet-window admissions were retried; none was launched.

## Final aggregation and audit

A900 compiled NDR_CombinedAudit unchanged: exit 0, 6.376899 s. Its enclosing
scope exited 3 because the own scanner compared merged duplicate-bearing
loader imports against the original index's stable-unique projection. It found
zero dangling edges. A900 took 85.086928 s, peaked at 12,214,488 KiB RSS,
swaps 0. The failure, source snapshots and diagnosis are retained, not erased.

V2 applies the identical stable first-occurrence projection used by
NER_ModuleTables.inspect and preserves raw loader lists. R031 tests dangling
recursor/body-removal behavior and rejects missing, extra and reordered import
mutations. R032 compiles the exact V2 driver. The scanner reads each own
declaration from the checked private kernel map. No model object was rebuilt
again for A901.

A901 loaded both roots together with importAll, private visibility and
initialized extensions, scanned the entire cohort, then used the unchanged
NEP hardened walker. Exit **0**; wall **103.193750 s**; peak RSS
**12,385,428 KiB**; swaps **0**. Caps: MemoryHigh 14G,
MemoryMax 16G, MemorySwapMax 0, TasksMax 64; Lean -M15000 -j1.
Source revision: `80cb4ac8876e51feeb9e7dc0ca620dcec50c0c1e`. Exact commands, source hashes,
limits, cgroup peak and both actual #print results are in NER_A901/receipt.json.
Process RSS and cgroup memory.peak are retained as different measurements.

| Root | Constants | Edges | Complete / equal collectAxioms |
|---|---:|---:|---|
| RPx_Deployed.deployed | 115,256 | 5,743,676 | yes / yes |
| NDR_CombinedAudit.sourceOnHeadline | 885,736 | 15,048,019 | yes / yes |

Both raw and summary sets are exactly Classical.choice, Quot.sound, propext.
The loaded scan covers 16,058 modules, 1,520,745 active declarations and
38,049,122 references: zero dangling edges and all canonical import lists match.
The 2,316,265 original serialized entries contain duplicates; their unique-name
count matches the loaded count module by module. This is not a missing-body gap.

All 34,043 selected/retained input files, including the Lean binary and walker,
were checked before and after A901. Original read-only objects remained intact.
The Stream B manifest is NER_STREAM_B_COHORT.jsonl.xz with its uncompressed
SHA-256 and metadata file. It includes available server/private/IR companions.
Source-basis qualifications for reused upstream objects remain explicit; all
1,387 rebuilt objects have exact source and selected-import compilation pins.

Usage: 37 batch scopes plus four focused scanner/driver controls in this
continuation (41/120 capped scopes), plus 28 historical focused scopes retained
from the earlier run; both agg16 allowances used. No uncapped Lean or cap raise.
NER_tests.py, NER_rebuild_checks.py and NER_final_checks.py validate the saved
evidence and matched mutations. Historical stage notes are in
NER_REBUILD_HISTORY.md; no unchanged successful Lean regression was repeated.

No cryptographic/refinement assumption was discharged, added or changed.
sourceOnHeadline remains quantified over base/stage/slot and conditional on
FixturePdaRuntime base. It retains the same 1,768-byte saved vector, both TX1
results and TX2 success, with distinct heaps explicit. This audit closes the
requested object-coherence gate; it does not establish the wider security target.
