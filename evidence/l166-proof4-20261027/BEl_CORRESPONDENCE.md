# Source/reference/model correspondence and open physical boundary

This table describes a direct Lean model and partial gates. It is NOT a full
Rust contextual-refinement certificate. **Whole instrumented shipped-body
Result/log equality remains open.** In particular, the failed full-batch Kani
runs do not become passing evidence through the Lean controller composition.

Frozen source: candidate.rs SHA-256
5164975df10f79e9810f9321b8130a9865eb9bb9b6b9de7011f4359ece98c794.
`BEl_generate.py --check` checks exact item bodies and full helper source pins.
`BEl_source_cuts.json` contains their bodies, hashes and visibility adaptations.
Reference locations below mean `BEl_rust/src/BEl_owned.rs`; generated original
source means `BEl_rust/src/BEl_frozen.rs`. Both are evidence-only proof crate
files, outside the shipped build. Harnesses are cfg(kani); fixtures cfg(test).
`BEl_observed.rs` exposes the caller-owned recorder for both complete bodies.

## Owned reference, line by line

| Reference lines | Source / meaning | Lean and actual validation scope |
|---|---|---|
| 1–4 | safe proof module, same Digest32/Error imports | no executable behavior |
| 6–13 | attempt owns concatenated address, all input parts, pending/returned marker | BEl_Recorder.Attempt; BEl_FullLog and CoordinateLog extensionality |
| 14–18 | Copy wrapper with shared private log; read old length | BEl_Recorder.History; K19 checks released guard at backend entry, one leaf call |
| 19–21 | copy every part and concatenate its bytes in order | K18 full Vec/Point projection on all three leaf grammars; arbitrary coordinates; NOT generic nine-part parent proof |
| 22 | append None BEFORE backend entry | BEl_Recorder.enter / PartialRecorder; K19 observes real pending entry |
| 23 | exactly one call to the actual backend on original borrowed parts | K19 observes entry; no backend stub; arbitrary reply for this one-call gate |
| 24–25 | complete same entry, return exact answer | Recorder.finish; K18/19 returned leaf marker checked |
| 28–32 | constant-reply backend | fixture / local-gate non-vacuity ONLY; not real SHA or whole adaptive experiment |
| 34–40 | tag/range leaf grammar; candidate.rs:117–131 | LeafReference.codeFor/code; K05–07 arbitrary bytes and reply; pure range-order proof |
| 43–47 | same proof, queries, root, ordinal, tree, live scratch; lo/n/slot | candidate.rs:173–176; BatchTree.code; counts10/12, ordinal0/1 |
| 48 | identical actual key construction and sorting | candidate.rs:177; inherited Op4/Op5/Port4B; helpers execute in whole probes, no stub |
| 49 | reset only logical used count, preserve scratch | candidate.rs:178; BatchTree/Loop; prior tree returns threaded |
| 50 | bounded for-position0..n, replacing while cursor | candidate.rs:179–182; BatchLoop all-fuel induction at n+1; direct-model correspondence, NOT successful whole-loop BMC |
| 51–54 | same sorted key, index, selected opening offset | candidate.rs:181–184; K21 same-allocation pointer/length, no copied synthetic proof |
| 55 | digest before deduplication | candidate.rs:185; K09–11 one exact leaf step, arbitrary scratch, d≤position<12 |
| 56–57 | matching index with unequal leaf rejects after that call | candidate.rs:186–190; same K09–11 status/state/coordinates |
| 58–59 | distinct index writes scratch then increments used | candidate.rs:192–194; K09–11 all arbitrary scratch coordinates, existing P6 insertion reused |
| 60–61 | continue to next key | BatchLoop induction; GateBounds counters give d≤position; no new scratch replay |
| 62 | actual node_count, same idx[..used], same Merkle error | candidate.rs:196; inherited P6 library/control lowering; no node_count stub |
| 63 | same physical slot slice | candidate.rs:197; inherited slot lowering and bounds; no fresh whole Rust gate passed |
| 64 | reject excessive count before padding | candidate.rs:199–200; inherited tail; GateBounds padding-domain arithmetic |
| 65–67 | same chunks_exact(8); per-word any-byte predicate | candidate.rs:199; K12 verifies every8-byte word predicate; whole traversal remains direct-model/library composition |
| 68 | actual verify_in_place on SAME live scratch and node prefix | candidate.rs:202; inherited P6 certificate/Port4B accepted scratch, reused read-only |
| 69–70 | same Ok/Merkle final result | candidate.rs:203–205; source controller observation theorem, no successful whole Rust BMC |
| 72–74 | zero scratch once; three sequential trees sharing scratch/backend/log | candidate.rs:162–168; Batch.values unrolls the three iterations and composes all outcomes |
| 75–76 | Ok only after all three returns | candidate.rs:169–170; same short-circuit source composition |

## Direct-model scope

The reference model uses the inherited source/library/P6 tail for the identical
node/verify helpers. Its padding and for-loop correspondence is recorded above;
it is not an Aeneas extraction of this new Rust crate. The owner allowed a direct
model with a line correspondence table; that allowance does not manufacture the
separate required shipped/reference physical Result/log certificate.

The accepted model observation deliberately forgets rejected error kind and
rejected mutable state as BEh permits. Logs retain duplicates and attempted
nonreturn. Rust Digest32 returns raw32 bytes, not Result; None at backend entry
means no return yet. PartialRecorder.decode labels a pending record using the
ambient observed stop; it does not claim Rust returned an Err.

K18 excludes only destruction of the dead audit log AFTER the observation cut
by forgetting it. It does not remove any shipped loop, call, scratch mutation
or cleanup. Caller-owned explicit logs are available in observed_shipped and
observed_reference. Their full equality passed four concrete slot/outcome
fixtures; those fixtures are not a universal certificate.
