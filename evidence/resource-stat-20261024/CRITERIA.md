# ResourceStat criteria (unadopted)

Scope: only tools/resource-stat-20261024 and evidence/resource-stat-20261024.
No builds, host mutations, scope reservations, consumer, key operations, merge or push.
Immutable baseline: 25b0b9df48; prior failures and captures remain unchanged.

Before implementation: assess official Linux 6.8 and exact Ubuntu kernel source,
including current/stat collection, charge stocks, rstat, hierarchy and read order.
A sum inequality across separately read interfaces is not an atomic invariant.
Implement only if useful as a conservative observation estimate, never a guarantee.

Before: disjoint exclusive stat > exclusive current denies.
After candidate: only uncovered cells with all existing component, subset,
unsigned, hierarchy and visibility checks valid can reserve max(current, sum)
with zero cache/slab credit. Covered inconsistency still denies. Across two
snapshots, either fallback zeros both credits; reserve maximum padded charge.
Root residual uses actual current, so padding is additional reservation.
All valid old estimates unchanged; all other denials and GO binding retained.
No tolerance, rounding, whitelist, suppressed reads, new trust or adoption.

Validation: retain all 57 historical tests explicitly; test exact recorded 4096
excess, large deficits, both directions, zero credits, unchanged valid estimates,
negative/nested/overcap/missing inputs, prospective and actual GO checks. Record
commands, exit, wall, RSS, swap, revision/hashes and N/A axioms. Offline ordered
replay must remain nonmutating. At most one optional live diagnostic after
source/test receipt commit; zero captures is acceptable if offline work suffices.
Security targets remain not yet established.
