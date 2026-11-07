# NMB native cut translation boundary

Target not yet established. No whole parent or row root is credited here.

K030 checks the exact three-operand owning-array constructor on full arbitrary
58295/1880/1768-byte vectors or deferred InvalidAccountData, arbitrary original
metadata and length words. Its empty modifies set is part of the assertion.
K031 fails the inverted header postcondition. K032 changes an OLD input byte
before constructing the array and fails specifically on assignability, so
consuming an OwnedAccount by value does NOT exempt its old payload from the
modifies check. All share canonical KMX, frozen offline graphs and unchanged
locks. This replaces the large byte-index comparison by header plus old-region
frame reasoning; it does not rerun a retired timeout.

Header equality must include error tags. K030's initial header view observes
only bytes.is_ok(), so K033/K034 supplement it with the exact deferred Err
constructor. No full-valued array claim is made before that pair passes.

NMB_ArrayFrame.Cut is the MODEL transcription of this LOCAL constructor
contract, not an arbitrary whole-function endpoint assumption. Its source
theorem uses full old-region contents, unchanged headers/error values and the
SAME allocation identity to derive full byte equality. The actual Rust/source
ownership map, live-allocation identity, no allocator call in the constructor,
and propagation of the Kani modifies semantics remain P6/Std/Allocator tool
transport under the existing owner-approved reclassification. They are not
new cryptographic assumptions or new runtime rows. A fresh allocation sharing
an integer address is not an admissible substitute for that identity.

The three snapshot calls have their OWN CLOSED343/NLF packets. Those packets
must relate each full native result to its original bytes at the SAME call;
array-constructor framing does not supply the snapshot copy law. Their
source-order SDK world chain is NMB_SnapshotChain.three. Native argument
reference fragments K023–028 are at source indices0/1/2, with exact thresholds
58295/1880/1768 and empty modifies. They are source-fragment contracts, not
standalone certificates for the complete frozen function.

No Ref/RefMut/Result<Box>/ProgramResult verified stub is used. NMB_fill is an
input-generator contract on an existing initialized fixed byte array; its
three complete interface-fidelity families pass before use. Private source
cleanup is expanded by NMB_Cleanup as logical destructor occurrences, NOT a
claim that Solana's bump allocator returns physical memory.

Review correction: K034 fails the nested header ensures before reaching the intended discriminant control. K033/K034 DO NOT establish a matched exact-error cut. Full error identity in NMB_ArrayFrame.Cut is therefore OPEN natively. K030/K031 only prove header/discriminant equality; their header does not distinguish ProgramError variants.
