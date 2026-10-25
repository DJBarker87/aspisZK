# Port12COUNT handoff

Branch codex/cx-port12count-20261024, reviewed base431346f953.

Delivered: unconditional all-input/all-H physical P6 node/row/height potential,
then actual BatchStep/Loop/Tree/Batch counts and installed op5 batch0<=477,
batch1<=563. The actual four owned installed call logs total<=1046. A concrete
owned-call checkpoint projection feeds the writer's saved Vec into current18
and its reply into batch1, with all errors short-circuiting; count<=1046.
Explicit first-read consumers use the proved total ordered log length, retaining
repeated source calls. See STAGE1.md and STAGE2.md for complete claims, runtime
domains, source paths and retained failure evidence.

The main theorem references are Port12COUNT_Verify.count,
Port12COUNT_BatchLoop.count, Port12COUNT_Installed.batch0/batch1/owned_calls/
checkpointChain_count and Port12COUNT_FirstReads.owned_calls/checkpointChain.
These are concrete physical source counts, not accepted-only model counts or
per-fuel wrappers. RowDomain follows from the actual reached P6 count guards;
all six actual capacity lookup premises are discharged. Arbitrary digest
failure/divergence policy is retained. No prior theorem premise was changed.

NOT delivered: a full driver1161 theorem. The owned-call projection is not
claimed equal to the full driver: delegated interleaved rest calls determine
actual arguments and can issue unbounded reads. Exact next producer is a
concrete rest implementation plus its all-outcome executed-call budget<=115,
and actual driver log/control-flow composition. Session A's existing
op3/op4/op7 producer request was not duplicated. Both deployed targets remain
NOT established; target(Q+34)*B+kappa(Q+1161)+2^-126+2^-454 unchanged.

Final audit: lean-029, Port12COUNT_Audit.lean, exit0, wall1.96390285299276s,
peak4414056KiB, swaps0, source revisioncd118a6bc6 with source/dependency hashes
in receipt. Full signatures/definitions and36 axiom reports are in stdout.log;
only propext/Classical.choice/Quot.sound. Twelve final module hashes match
green focused receipts. verification.json records local static validation.

Every actual Lean launch used an independently capped6G/8G/noSwap/Tasks64
scope, -j1/-M4400/async=false and the shared global lock. Reservations were
checked below55GiB. All failures and command/source/dependency/resource/axiom
receipts are retained. Cached source/refinement and checkpoint component
objects were explicitly reused; no coherent frozen manifest or new ELF identity
gate, runtime suite, Rust gate or Kani was run. No cap/heartbeat/recursion
limit was raised and no unchanged resource failure was rerun.

Budget:28 actual Lean attempts here,185 inherited =>213/220 used,7 actual
remain. One pre-Lean missing-object rejection is preserved as allocated slot007;
29 slots allocated =>6 conservatively unreserved. Earlier manifests counted
that reservation conservatively as an attempt; final ledger distinguishes
actual launches from allocation without resetting or discarding it. Kani0/20,
20 remain. No job remains running.

New Port12COUNT modules/tools/evidence only. No shipped source, crates/programs,
backend, protocol, wire, feature, security contract, key, Session A candidate,
merge or push changes.
