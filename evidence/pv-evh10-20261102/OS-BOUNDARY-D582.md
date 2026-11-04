# D582 — mapped permissions and the same-prefix Linux copy boundary

Resume base `f9881c743b`, branch `codex/pv-evh-20261029`.
Evidence class: **binary-structural (adopted binary), plus OS-model**;
source/machine correspondence remains **V370 compiler-cohort** under l3-1.
This document is a structural interpretation, not an elaborated Lean theorem,
a machine proof of Linux/compiler correctness, or an observation of a deployed
process. The adopted binary remains `da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0`.

`os-model-D582/manifest.json` pins the complete reference Linux v6.8 sources
used below. v6.8 is an explicit reference OS model, **not a claim that the
adopted client was deployed on that kernel**. The Linux API/uaccess contract is
the OS boundary requested for this analysis. Kernel RNG internals remain under
the existing `entropy_kernel` T field; this supplies no additional T field.

## Fixed prefix and shared OWNER dependency

Keep D580/D581's four binders and actual reached-prefix domain unchanged.
Every address below uses q's actual process, stack pointer and load bias.
Faults, errors, retries, exhaustion and later rejection remain in the domain.
The world is the source world paired with THAT machine prefix at
`opsNative (rawBase base) heap box ops`; it is not an independently chosen world.

The single named **owner interpretation dependency** is
`OWNER_actual_prefix` from pv-evhB4, to be consumed only after the lead merges
it. This is a dependency name, not a new local Lean declaration or an invented
replacement owner relation. It must connect the existing runtime heap's Vec /
RawVec allocations and the existing live stack slots to the same process,
allocator world, activation and byte memory; establish lifetime/separation
facts needed for heap/live exclusion; and preserve that relation on reached
transitions. This job does not supply or implement it. The exact exported
module/theorem name will be recorded after the lead's merge.

Mapped permissions are properties of the process's address-space mappings;
owner identity is a different property. A mapped RW region alone says nothing
about which abstract Vec, RawVec or source lifetime owns its bytes.

## Permission interpretation

For a machine prefix q, `mappedRW(q,p)` means p lies in a current user VMA
of q's `mm` with VM_READ and VM_WRITE (and access allowed by the current
architecture protection state). This does not mean that a physical page is
resident: permitted demand paging is part of the Linux model. Legal future
stack expansion and membership in a current VMA are also distinct.

The ELF PT_LOAD flags determine image permissions through
`fs/binfmt_elf.c:make_prot`; image mappings use MAP_PRIVATE. PT_GNU_STACK is an
execution-policy request for the process stack, not a loadable stack segment.
Linux `fs/exec.c:setup_arg_pages` installs the stack VMA, with stack default
read/write permissions (`include/linux/mm.h:VM_STACK_FLAGS`). Its initial
extension is capped by RLIMIT_STACK. `mm/mmap.c:do_brk_flags` supplies RW data
mapping flags; anonymous allocator mappings use their requested protections.
Heap allocations must be inside those actual current writable mappings; an
ELF data segment is not evidence for all later malloc allocations. Binding
existing abstract blocks to those allocations belongs to `OWNER_actual_prefix`.

“By this process only” here means its private address space and private
writable pages, with Linux fork/COW semantics. A numeric address in another
process denotes that process's mapping, not this allocation. Threads using
CLONE_VM share the address space (`kernel/fork.c:copy_mm`). Kernel access,
authorized tracing, explicit shared mappings and signal handlers are not
excluded by the word private. No process-private-memory claim establishes
L3 secrecy, register erasure, core-dump exclusion, or V371.

N91602 verifies PT_GNU_STACK RW, with no execute flag. The loadable image
requests R at [0,0x466d8), RX at [0x476e0,0x1dfdc0), and RW at
[0x1e0dc0,0x1ea000) and [0x1ea2b8,0x1eb5e0), before page rounding and
relocation by q's load bias. GNU_RELRO covers [0x1e0dc0,0x1ea000);
post-relocation permissions there may be read-only. These are image ranges,
not the runtime stack or malloc heap.

For any actual stack VMA [S,E) with the above RW policy, the elementary
structural implication is:

```text
S <= sp(q) and sp(q)+232 <= E
  -> forall i<232, mappedRW(q, sp(q)+i)
```

The same implication applies to actual owned heap intervals inside current
RW allocation mappings; the abstract-block membership is deferred to OWNER.
Mapped RW does not guarantee future fault-free execution or resource adequacy.

**Exact limit:** the ELF and Linux setup determine the region's permission
policy, not the current bounds S,E of every actual reached stack. The
predecessors inspected in N91602 reserve 184 bytes plus four pushes (`open`)
and 472 plus six pushes (`Accounts::parse`); mere subtraction is not a
permission probe. No all-path lower-bound proof from their deeper callees
has been supplied. D581's plan probes also precede subsequent downward call
reservations. The fixed domain does not carry an actual mapping history.

The missing inference cannot be justified by alignment alone: if a stack
VMA starts at a page boundary L, a 16-aligned prospective sp=L-16 has
its saved-register bytes at sp+232 inside that VMA, while 16 frame bytes
are below it. Linux may extend the grow-down stack on a later fault or
terminate on a resource/guard failure. This is an arithmetic counterexample
to that inference, **not a checked shipped-source counterexample** and not
a manufactured member of ActualEntropyEntryPrefix. Access_ok similarly does
not prove current VMA coverage.

Consequently, part (b)'s **permission-class interpretation** is supplied, but
its universal actual 232-byte coverage assertion is not discharged. To make
OWNER the only remaining input to actual_frame_entry still requires deriving
that coverage from the actual stack setup and preceding accesses, on the
unchanged prefix domain. It must not be put inside the owner dependency or
replaced by future-success/stack-admission membership.

## Same-prefix kernel association

At the reached syscall PC `load_bias(q)+0x145817`, D581 binds the first request
to RAX=318, RDI=sp, RSI=64, RDX=0. Linux's x86_64 syscall table identifies
318 as getrandom. At later partial calls let `a=sp(q)`, `o` be the driver's
consumed count, `u=a+o`, `n=64-o`, with 0<=o<=64. The positive-result branch
advances u and decreases n; EINTR retries the same suffix. No libc/dlsym call
or independent destination buffer is inserted.

For each actual reached syscall use this event correspondence, in order:

| Component | Interpretation at this same prefix |
|---|---|
| Request | Actual syscall instruction, registers u,n,0 and actual calling task/mm. |
| Before | Process byte memory immediately before this syscall's payload-copy effects; previously consumed bytes are included. |
| Payload copy | getrandom imports one ITER_DEST user buffer, then copies only through that bounded iterator. Kernel temporary RNG state is kernel-side OS state. |
| Reply buffer | Decode all 64 actual user bytes after the copy boundary, including unchanged bytes and any partial write; never fabricate a whole entropy answer from the return value. |
| Reply result | Actual signed RAX/error/terminal prefix, using the existing LinuxRaw ABI and control conversion. |
| World/events | Ordered OS/native events of that very execution segment, including wait, fault, interruption and timing/resource effects. They are not [] by convention and not taken from a second run. |

The OS-model write-footprint derivation is as follows. `random.c:getrandom`
validates flags and readiness, then `import_ubuf(ITER_DEST,u,n,...)` installs
one destination iterator. Here n<=64, so MAX_RW_COUNT truncation does not
change n. `include/linux/uio.h:iov_iter_ubuf` sets its base and count from
that same request. `include/linux/iov_iter.h:iterate_and_advance2` clamps
each copy to the iterator's remaining count; `iterate_ubuf` advances by the
actual number copied. `lib/iov_iter.c:copy_to_user_iter` reaches
`raw_copy_to_user`, whose contract in `include/linux/uaccess.h` confines
stores to the supplied range and preserves its uncopied suffix. Thus all
payload writes are in [u,u+n), and successful full delivery fills that
interval. The syscall does **not** promise that every error/partial return
writes n bytes. Its return and partially changed memory must both survive.

No kernel-side entropy copy is another user-space owner, stack spill, or new
secret array in `StackZero.State`. It is the specified OS boundary. This does
not claim that kernel buffers do not exist or are physically inaccessible to
a privileged observer. Kernel-side randomness stays within `entropy_kernel`;
existing observation/V371/L3 obligations remain unchanged.

Let `m_before` and `m_after` be those same payload-boundary byte projections,
and let `buf_after` be the lossless U8 decode of actual bytes [a,a+64).
The structural conclusion on EVERY reached copy boundary is exactly:

```text
Backed a buf_after m_after
forall p, p < a+o or a+64 <= p -> m_after p = m_before p
```

This is `PV_EVH_KernelMemory.Step a o m_before m_after buf_after`, by the
existing definition, with no assumption about eventual successful entropy.
`StackByteCodec` supplies the existing encode/decode value bridge.
This is a structural OS-model instance specification, not a new Lean proof.
It does not assert the stronger `ValidAnswer` over arbitrary unreached worlds,
buffers and memories. The per-reached-call consumer is
`PV_EVH_RawMemoryHistory.threaded`'s `hv`, then
`PV_EVH_RawMemoryReification.driver_memory` when its history is supplied.

“Nothing else” refers to this syscall's **user payload writes**. RAX/RCX/R11,
kernel bookkeeping, page tables and OS events change too. Signal delivery
may write a user signal frame; another thread can write shared address-space
bytes. Such transitions must remain explicit interleaved events/world steps,
not be attributed to getrandom's payload or erased to make a whole elapsed
syscall interval satisfy Step. This boundary distinction is necessary to
preserve the same-prefix memory/history correspondence. Installation of that
advancing complete execution is still required before the five projections.
