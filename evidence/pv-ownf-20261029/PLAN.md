# D436 own-2' qualification

Work only in the existing sparse `/Users/dominic/ZK/.worktrees/pv-own`, branch
`codex/pv-ownf-20261029`, base `95971605dd`. No implementation changes.
New Lean names, if required, use PV_OWNF_; IDs 63500–63599 only, audits
63597–63599. Budget: 60 Lean attempts, 30 capped native scopes, zero Kani.

1. Revalidate the inherited 44-source call-cone capture against HEAD and the
   pinned host files. Apply the allocator-internal exemption to initialization,
   arena, chunk, tcache and allocator-local TLS reads, including the two
   original rejection witnesses.
2. Expand allocator-entry inspection beyond the old two witnesses. Classify
   shared process/thread state separately from allocator-owned state. Stop each
   row upon a checked OTHER read, as the user explicitly requires.
3. Only if qualification passes: prove source address independence, then named
   model Result literal laws, one deployed release execution per root with
   byte comparison and crate fingerprint cross-checks, and allocation/abort
   treatment under rdea-1. Use compliant scopes, one at a time.
4. Record exact statuses, evidence classes, retained obligations and budgets.
   Commit each completed stage, never push or merge.

Initial expanded inspection identifies a possible OTHER read at
`__libc_malloc+0x65`: process-wide `__libc_single_threaded`, with an external
writer in `pthread_create`. Verify its symbol, writable section, semantic
header, read and writer against the same pinned libc before deciding status.
No formal release result or deployed function execution is yet claimed.
