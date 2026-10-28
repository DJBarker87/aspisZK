# Combined statement audit

Target not yet established. This is a scoped source-law package, not a new
privacy theorem or an endpoint premise-removal claim. Evidence class:
**structural (K-1 substitute)**, with native differentials as finite validation.

## Exact statements and carriers

The original ExternalTypes and ExternalFuns carriers are unchanged. DropSelected
updates only op4 at Vec U32 and retains op4 for other types. ZeroSelected updates
only op122/op123. ReserveSelected updates only op32, as a family indexed by the
current allocator world and runtime metadata. AuditInstall composes those updates
and proves that restoring the four old fields recovers the entire original record.
This checks every other field, not selected samples. Closure.callbacks exercises
the exact emitted primitive byte dictionaries and the source error encoding.

No fixed world-free generic destructor claim is restored. The accepted generic
counterexample remains in DropCounterexample and FINDING.md. The finite op4 census
contains exactly one call at ProverRwFullFuns:16098, host_tree.rs:29, T=Vec<u32>.
This is a narrower, explicitly recorded statement authorized by D362.

For op122/op123 the generic value projection sequences the supplied callbacks
and Default Result. The complete physical zero-byte law is at the emitted u8
DefaultIsZeroes/Zeroize dictionaries, not at arbitrary custom trait dictionaries.
ZeroConsumed imports and identifies the actual ProverRwFull constructors; the
source secret arrays have N=32 or 64, and the theorem handles all N symbolically.
ZeroDrop links the consuming Zeroizing::drop delegation and consumes the value.
No generic custom trait effect is silently declared pure or physically zero.

## State and execution

Allocator-visible physical memory and every accessible external effect are inside
Physical.Runtime. An allocator can change those on either success or failure.
The separate disjoint frame is the only frame kept unchanged. The `memory` fields
of the allocation models are logical allocation snapshots governed by `live`;
they are not claims that free preserves or clears physical freed storage.

Drop: no u32 user destructor; one semantic Vec::drop and RawVec::drop entry;
free iff capacity nonzero, size=4*capacity/alignment=4. The allocation is consumed.
The primitive free transition is preserved, including physical/external effects.

Reserve: shape/layout and buffer address/capacity are runtime metadata, not inferred
from the extracted list. The source's spare-capacity, zero-size, checked-add,
checked-layout and allocator-error paths are all represented. Failure leaves the
vector and logical buffer unchanged while retaining allocator state/history and
attempt counts. Success keeps values/len, installs the pointer and requested
capacity, and records allocation or realloc. ReserveCaller passes the entire
post-buffer header to the continuation and constructs postMetadata; a later push
must not reuse the old capacity. The source/reference equality is parameterized
by the same raw allocate/realloc primitives. ReservePrimitive proves exact call
arguments, including omission of the dangling pointer for fresh allocation.
ReserveLayout justifies every normalized pure guard and same-alignment branch.

Zeroize: every target byte is overwritten by a volatile-zero event followed by
a SeqCst compiler-fence event. Counts and exact chronological history are proved,
including already-zero input bytes. Outside-target data and the disjoint frame
are preserved; no allocator/element destructor is invoked by byte zeroize.
The complete returned value and post-write state are passed to the continuation.
No extracted mutable iterator or discarded restoration continuation is imported.

## Hypotheses and remaining obligations

Operational primitive functions, initial states, runtime metadata and caller
continuations are explicit universally quantified inputs, not added T fields or
structures containing the desired source law. Buffer.fits is the ordinary valid
owned-vector len<=capacity condition. ReserveSelected.error_payload's type equality
identifies the already selected op5 carrier (PDict_FinalTypes.type5_installed /
PDict_IOCarriers.native); it does not assume allocator success or error behavior.
Its canonical encoding retains CapacityOverflow and the complete requested Layout
in AllocError, including the non_exhaustive Unit field.

The source laws compare the same returning raw primitives in native/control and
owned references. They do not prove libc internals, arbitrary OS nonreturn,
compiler correctness, or deployed binary correspondence. Those realization and
whole-prover execution obligations remain P. The allocator failure event's
witness-independence is not established by a local Result/state equation.

A compiler fence is not a hardware fence. The source gate proves calls to volatile
writes and compiler fences in the required order under their Rust primitive
interpretation. It does not audit actual deployed instructions, register/spill/
extra-copy erasure, persistence or L1/L2/L3 observations. The L3 binary audit stays
separate. No observer, simulator, failure signal, quantifier in an endpoint or
privacy bound is changed. T remains exactly entropy_law, entropy_kernel,
observation. No deployment, E1/E2, real RunJoin or side-channel premise is removed.

## Verification

Each changed generic module was compiled alone before its dependent target.
Only accepted standard axioms are credited. Failed elaborations, two private
output/import environment errors, refusals and a cooldown scheduling deviation
are retained. All compiler runs used -M7000, 6G/8G/swap 0 caps; native work used -O.
No Kani or ELF rebuild. All added theorem statements receive #print axioms.
The final combined audit is separate from the one focused closure replay.
Neither packaging imports nor packaging a conjunction is counted as additional
security progress. Exact revisions, source blobs/hashes, dependency fingerprints,
exit/wall/RSS/swap and raw axioms are in each numbered receipt.
