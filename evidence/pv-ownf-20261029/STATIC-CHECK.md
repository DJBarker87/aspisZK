# D436: own-2' complete-cone qualification has OTHER reads

V229 and V230 remain **SUSPENDED under own-1**. This is a negative
qualification certificate, not a positive complete-cone purity certificate or
a witness-dependent privacy FINDING. One reachable OTHER read suffices to
refute the universal condition; no remaining unexamined callee is declared
pure. The instruction to stop each row on an OTHER read applies before the
conditional value/native-execution work.

The old two witnesses now classify as **ALLOCATOR-INTERNAL**, and are allowed:
`__libc_malloc` at `0xad764` reads its initialization byte `0x20b188`;
`0xad79a` reads its tcache TLS. Neither is reused as an own-2' rejection.

## New success-path OTHER reads

### Process-wide threading flag

At `__libc_malloc+0x65`, instruction `0xad7b5` reads the exported byte
`__libc_single_threaded` at ELF virtual address `0x20c040`. The dynamic symbol
table places this one-byte object in writable `.bss`. The installed glibc
header `sys/single_threaded.h` defines its meaning: nonzero means the current
thread is the only thread in the process image; zero permits a multithreaded
process. This is process state shared with the threading implementation,
not an allocator-owned arena, chunk or tcache field.

The same pinned libc's `pthread_create` reads it at `0x9cce3` and writes zero
to it at `0x9d336`. This writer is outside alloc/realloc/dealloc. It establishes
that the state is not confined to the allocator's own internals. I therefore
classify this read **OTHER** under the stated confinement requirement, even
though this particular read occurs inside malloc.

It is reachable for the mandatory first request1016/alignment2 when that
size's tcache entry is empty (or tcache is absent): `0xad89d` tests the cache
count, and `0xad8a0` branches to `0xad7b5` on zero. No source or admission
precondition requires that cache bin to contain a free entry. This is normal
successful-allocation control flow, not the allocation-failure handler.
The check does not assert the branch is taken on every call.

### General errno TLS saved by free

At `__libc_free+0x29`, `0xade59` loads the calling thread's incoming errno into
`r12d` through `%fs:(%rbx)`. The immediately preceding load at `0xade4e` obtains
its TLS offset through ELF slot `0x203df8`. Independently, `__errno_location`
at `0x2a6e4` loads that **same slot**, then adds the thread base at `0x2a6eb`.
The installed `errno.h` maps errno to `*__errno_location()`.

Normal free restores the saved error value at `0xadeae` (the mmap alternative
at `0xadefa`). Preservation does not turn the read into allocator-owned state:
it reads general pre-existing per-thread error state. I classify it **OTHER**.
It is an additional witness; rejection does not depend on establishing every
later destructor path, since the first malloc witness already suffices.
Both functions also reach nonnull free when their intermediate Link Vec is
consumed; V230 additionally drops the final row Vec before returning its array.

The exemption is specifically for the allocator's *own internal state*. It
is not interpreted here as permission for every external datum merely because
a read instruction lies inside libc malloc/free. No broader exception for
process-threading flags or preserved incoming errno was supplied. Neither
read is claimed to affect the returned u16 values, and neither supplies a
same-public witness pair with different D159 observations.

## Revalidated source and runtime chain

`tools/pv-ownf-20261029/static-check.py` validates all44 inherited source files
against their actual host paths, sizes and SHA256s and rechecks all six
application/configuration files against this branch's HEAD. The full source
texts remain in `../pv-owne-20261029/static-capture.json`; the new capture pins
that exact file's SHA256. No old rejection classification is promoted to a
positive certificate.

The root chain is unchanged: V230 at forest198–205 calls V229 at184–195;
V229 calls the forest builder119–181; that builder unconditionally calls the
legacy builder, whose first operation at tree105–107 is
`Vec::with_capacity(127)`. Vec→RawVec→Global→`__rust_alloc`→`__rdl_alloc`→
System→malloc is pinned by the retained1.94.1 sources and original deployed
client disassembly. Source Drop→RawVec→Global→System→free is retained too.

The inherited source review covers both link constructors and endpoint
counters, fixed profile/path helpers, source IntoIter, Filter, FlatMap,
Map/FlattenCompat/Fuse, array iterators, collect specialization and fallback,
reserve/growth, guards, unstable sort's pivot/partition/heapsort/smallsort,
dedup moves, mask fold, allocator and abort entry points. Expanding the runtime
entry review exposes the new OTHER reads. Checking the complete-cone
*condition* fails at these edges; no exhaustive libc transitive-read inventory
is asserted after rejection.

The capture retains full malloc/realloc/free, errno-location and
pthread-create disassembly, dynamic symbols, section table, build notes,
headers, toolchain and libc version. The allocator-state accesses in the old
capture remain allowed under own-2'. Failure-only `rust_oom` HOOK access stays
under **rdea-1**, as before; it is not a new rejection witness or trust item.

Pinned baseline client SHA256:
`fa888460b2c37bee087afd6289cd55219fe2732ea1e1c75011147ed15c260348`.
Pinned glibc2.39 SHA256:
`3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf`;
ELF build ID `a4a7992a8e66555c8141ab2a08a8465ff6e0ea65`.
These files were inspected read-only, not executed as requested root calls.

## Consequences and proof limits

The conditional address-independence proof and own-2(a)–(c) are **not reached**
after the required OTHER-read stop. Ordinary source inspection still finds
no application pointer-to-integer cast or address hash in either root.
Library iterators/collect/sort do compare cursors and compute pointer
differences; this report does not mislabel their presence as an address-
independence proof. No positive relocation-invariance certificate is claimed.

No new Result literal law, release execution, byte comparison, crate
fingerprint cross-check or allocation trace was performed. Existing named
PV_RDB2D_ op133 and mask-loop value laws and previous finite allocation/null
injection results remain supporting evidence without promotion. The class
**“exhaustive over a singleton input domain, deployed compiled artifact”**
is **not assigned**. There is no source-binding proof or universal native law.
