# D435 own-2 qualification

Worktree exactly `/Users/dominic/ZK/.worktrees/pv-own`, branch
`codex/pv-owne-20261029`, candidate `325ba5f047`.
Budget: at most 60 Lean starts (63400–63499; audits 63497–63499),
30 capped native scopes, zero Kani. No subagents.

1. Inspect both no-argument application bodies and their shared legacy/forest
   schedule, link, endpoint counters, constants and helper branches.
2. Inspect rust-src 1.94.1 iterator, Filter/FlatMap, array/Vec IntoIter,
   FromIterator/collector specializations and guards, reserve/growth,
   sort_unstable (including pivots, partitions, smallsort and heapsort),
   dedup and destructors. Include allocator dispatch and failure entry points.
3. Test own-2's complete-cone no-external-read condition before value proofs
   or execution. Pin sources, runtime and existing deployed client identity.
   A mandatory external read rejects qualification for both callers;
   record it and stop those rows under own-1, as explicitly requested.
   Do not reinterpret rdea-1 as an unwritten exemption from this condition.
4. Only for qualifying rows: named literal Result proofs, smallest focused
   compilation first; one admitted capped deployed release execution per
   function, byte comparison and fingerprint cross-checks; allocation and
   abort record; combined statements/axioms audit and focused replay.
5. Preserve all prior own-1 work and its exact remaining blockers; report
   row status and premise accounting. Commit only this task's paths; no push.

Allocation failure remains under rdea-1. A successful allocator-path TLS
read is a qualification obstruction, not a same-public witness counterexample.
