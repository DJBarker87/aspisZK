# Retained failed approaches

All prior failures, raw captures, old coverage limits and test results at
25b0b9df48 remain immutable. This packet does not repair those files.
The old sum gate still rejects the fitness-worker AFTER input; replay confirms
all seven historical recorded decisions byte-for-byte at the object level.

Initial ResourceStat tests command:
`python3 -B tools/resource-stat-20261024/ResourceStat_tests.py`
(exit 1, tool wall 0.313294125s; peak RSS/swap not captured on this initial
unwrapped run, explicitly unknown, revision 47cf57ceca with uncommitted candidate;
N/A axioms). Full output: tests-first.log. Historical 57 passed; candidate 64
had one failure: the unchanged historical transport emits ResourceGO-phase-v1
while candidate API now emits ResourceStat-GO-phase-v1. This tested a copied
historical collector, not a ResourceStat collector. The test adapter now scopes
the historical schema expectation only around that historical mock transport;
no live collector was changed or run. Candidate decision schemas stay versioned.
The first source hashes were not retained before the test-adapter edit; do not
attribute the final source digest to that failed run. Final measured runs have
complete hashes/receipts. This evidence limitation is not silently filled in.

Explicit expected-denial contract change: historical
`CandidateTests.test_components_exceed_current` checks (slab=101,inactive=0)
and (slab=60,inactive=60), current=100. Historical tests remain byte-identical.
The candidate adapter retains denial for individual 101>100; the second case
now reserves 120 with both credits zero. This is the only denial expectation
changed. Covered inconsistency remains a denial. The candidate is unadopted.

The Linux sum-as-disjoint claim itself is false in general: lazy-free mapped
anonymous pages can also occupy file LRU lists. No claim is made that this
caused the recorded service excess. Temporal/rstat/stock effects cannot be
resolved into a unique cause from the available read pair.

A later attempt to produce a separately timed refresh receipt for all primary
URLs failed with HTTP 429 (Too Many Requests). `sources.log` and
`sources-receipt.json` preserve exit 1, 7.251391790807247s, 29081600B peak RSS,
swap 0 and exact source/dependency hashes/command/revision. No retry was made.
The refresh script writes its reference bundle only at completion, so partial
refresh results and the failing URL are unknown. This does not invalidate the
six earlier successful exact-Ubuntu tagged retrieval hashes; those earlier
retrievals were not separately timed. Official documentation and upstream
source were also read through the browser. Do not report a successful nine-URL
refresh or a measured successful retrieval run.
