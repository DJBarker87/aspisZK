# Exact two-element finish prefix

**Proved:** the emitted `core.array.Array.index (IndexSlice RangeTo{end=2})` on an array of length2 returns its complete slice. Any success of this operation returns that exact slice; each successful slice read is the same array read at the same index.

This proves the operation used in the existing S2 `finish_relation` trace, reusing the concrete range-operation expansion used by S2 frame proofs. It supplies exact slice/read identity instead of assuming an input relation. Its only compiled import is Aeneas; no arithmetic, sampler, hash or allocation assumptions are introduced.

One focused target passed with standard axioms, M4400, one thread, root atomic mutex, 7.5GiB aggregate stop and120s watchdog; zero swap. Exact source/revision/object/command/profile/limits are retained. Three small source/API failures are preserved as unaccepted diagnostics; they are not accepted axioms. No binaries, full closure inventory or manifest replay is included.

The enclosing caller still has to connect this source operation and its nominal carriers to actual Pair input. This leaf does not establish actual caller/runtime or100-bit soundness.
