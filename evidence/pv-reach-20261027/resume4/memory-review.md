# Isolated generated matcher failure and replacement

Attempt 37325, `ComposedChunk003` (`validate_pool_v1_context`), failed with
Lean `memory_exception` under -M7000, same 6G/8G/swap0 cgroup. Peak RSS
7,342,288,896 bytes; wall 44.567 s; swaps 0. The launcher-level exit is 0,
but the target is rejected because the log reports excessive memory and a
core dump. No passing compiler exit is inferred from that launcher exit.

The generator entered a generated literal matcher for two U64 layout
fingerprints and did not establish symbolic constructor progress. It was
changed to process constructor casesOn recursors only; generated literal
matchers stay explicit unresolved leaf boundaries. This permanently prevents
that matcher shape from triggering normalization/recursive reinspection.
No cap/heartbeat/recursion limit is raised. Attempt 37333 checks the changed
generator; 37334 checks the affected chunk with changed dependencies. This
replacement does not claim the literal match's internal callback coverage.

The queue was paused and ended; independent completed checks 37326–37332 are
retained. No unchanged retry of the failed chunk occurred. The local attempt
to allocate 37331 for the generator was rejected before reservation/compile
because the queue had already used that ID; the generator uses 37333 instead.
