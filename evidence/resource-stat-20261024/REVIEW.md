# ResourceStat handoff — candidate only, not adopted

Branch: codex/cx-resource-stat-20261024. Entry: 25b0b9df48.
Criteria: 47cf57ceca. Source/tests/audit packet: 5fc0adb848.
Only assigned tools/evidence paths changed; no merge/push, host operations,
scopes/reservations/consumer, compiler/build/extraction/backend/ELF, key or
shipped source/contract/trust changes. All earlier packets remain immutable.

## Established claim

Linux 6.8 and exact Ubuntu-6.8.0-147.147 source do not guarantee the packet's
sum<=current across separately ordered reads. Different page-counter/stat paths,
per-CPU charge stocks, conditional/asynchronous rstat flushing, hierarchical
propagation and traversal timing preclude an atomic interpretation. Additionally,
lazy-free mapped anonymous pages can occupy file LRU lists: the historical
"disjoint" label is not a universal disjointness theorem. This does not identify
the cause of the service's recorded 4096 excess. See ASSESSMENT.md for complete
before/after premises, equations, source URLs/symbols and preservation argument.

The executable candidate handles only an otherwise valid uncovered cell's sum
excess: charge max(actual exclusive current, recorded sum), zero all cell credits,
retain raw discrepancy. Either snapshot fallback zeros both pair credits and
retains maximum conservative charge. Root residual uses actual current and is
fully charged. Covered inconsistencies, individual/subset/unsigned/errors and
all inherited visibility/membership/control checks continue to deny. No old
valid numeric estimate changes. This is conservative relative to observations
and the old credit formula, not a bound on unseen/current/future physical usage.

## New offline validation and reused observations

57 historical tests passed unchanged; 57 candidate compatibility tests plus
seven new tests passed. The one denial contract change and historical transport
schema adapter are explicit in FAILURES.md. Exact recorded 4096 reproducer and
both directions pass in audit, alongside synthetic large deficit/zero-credit,
valid-estimate preservation, nested/negative/overflow/subset/overcap/missing
cases, root/empty/threaded coverage, prospective and synthetic GO/count-once.

Complete ordered replay: BEFORE 6876 events, AFTER 6876, legacy 835; every raw
input shard/hash verified, both self identities replayed, legacy process/service/
Docker commands replayed in order. All original recorded decisions remain
unchanged denials. Reused pair: 116 nodes, 1313 TIDs each; no new measurement.
Candidate schemas are ResourceStat20261024-proposal-v1 and ResourceStat-GO-phase-v1.

Final test receipt: exit 0, 0.40061779180541635s, peak 37617664B, swap 0.
Final audit receipt: exit 0, 1.3310254169628024s, peak 81199104B, swap 0.
Commands, interpreter, source revision, all source/dependency hashes, input
manifest hash and N/A axioms are in *-receipt.json. commit-linkage.json confirms
those exact source hashes match 5fc0adb848. Every derived JSON is below 5MB.
Initial fixture/schema failure and timed HTTP429 refresh failure retained;
initial unwrapped test/primary-fetch measurement limitations are explicit.
No unchanged regression rerun after the final successful runs.

## Historical estimate, actual denial, recommendation

On the reused GO pair only: candidate prospective 1/2/3/4GiB passes its estimate;
6/7/8GiB denies. The 4GiB estimate is 66568970944B against 66698661888B total:
129690944B additional margin after the explicit 7GiB control reserve.
The service AFTER U=12107776, sum=12111872, excess=4096; pair charge=12115968
because BEFORE actual current was larger. Both pair credits are zero. Root
residuals remain 2247208960 and 2240557056B. Frontier=26172456960B (24.375GiB).
The older 109MiB/4GiB margin belongs to a different historical packet and remains
historical evidence only. Neither is current host headroom or launch authority.

Actual collector GO still denies: observed unlimited controls differ from
6G/8G/swap0/tasks64. Successful GO is synthetic only; no real capped consumer
has been established. Current host headroom remains unknown. Zero new host
captures were chosen because the offline pair resolves this semantic obstruction
and another diagnostic would not establish an authorized capped consumer.

Recommend further lead review of the estimate, not adoption or launch. The
remaining practical deliverable requires separately authorized actual capped
consumer binding and contemporary evidence. Retained inactive/half-slab credits
are estimates, not reclaim promises. No new trust assumption is introduced and
no atomic-memory or scheduler guarantee is claimed. Both native/spend-security
and crypto/privacy security targets remain not yet established; no theorem closes.

Safe nonmutating review entrypoints are documented in tools/resource-stat-20261024/README.md.
They write only this evidence directory and never call historical operational
main functions. No full frozen manifest or other release suite ran.
