# Closed current prefix composition packet

Frozen target: crates/aspis-r1-cost-probe/src/verifier.rs::batch_prefix_products,
revision4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Current root domain is a valid
shared M31 slice of length5*n,0<=n<=22, arbitrary raw words, with successful
standard allocation. The native M31 carrier maps losslessly to its raw U32;
size/alignment and every initial live window are checked in the native gates.
This does not establish the enclosing geometry's gathering/allocation history.

One initialized prefix Vec has len=index<5*n,cap=5*n. Only its logical old
words are initialized in the harness; spare capacity remains MaybeUninit.
The native source step reads flat[index], pushes the old product, records one
opaque M31 product call with those exact operands and arbitrary reply, and
increments index. All old live prefix locations and every flat location are
universally framed by symbolic offsets; the new cell, length, capacity, live
pointer, local log and returned product/index are checked together at the
same prestate. No field multiplication body executes. The only native loop
unwind is for harness prestate construction (at most109 writes), not for the
algorithm's iteration sequence. Twenty-two disjoint capacity classes cover
all nonempty current root sizes. A matched appended-cell corruption fails in
each class. Exact KMX pointer-copy controls use the identical source packet.

NET_prefix_source.py checks token-exact erasure against the frozen one-step
body, its typed M31 target, initialization and loop guard. Eight mutation
tests reject changed operands, order, index, frame setup and capacity coverage.
This is a checked semantic-transport certificate under approved P6/D188 option
A, not a theorem that a Rust source parser or compiler is verified.

NEI_PrefixWindows.source_step consumes precisely the same length and indexed
append/frame observations and the exact modular product reply to identify the
emitted NEG step. Its field-reply theorem selects the emitted natural product
from the native log's larger arbitrary-reply domain. The caller's raw word
inputs are unrestricted. NCB_PrefixCutTrace then composes ordered steps on
ONE evolving Vec; Port4C_PrefixMeaning supplies finite induction to the
installed S7Kani2PrefixLoop model. NET_PrefixClosure makes the current capacity
invariant and whole observed-Result consumer explicit. Imported proofs are
reused and hash-pinned; no stand-in loop or independently chosen output is used.

NET_L029 audits the actual extracted M31 product pairing and every new prefix
theorem using only propext, Classical.choice and Quot.sound. The failed L024
import is excluded; nine unchanged missing dependency modules were rebuilt
privately in L019..023/L025..028 with committed source provenance.

K085/K086 establish the exact empty constructor length/capacity for all
0<=n<=110 with a failing capacity control. K087/K088 establish the ACTUAL
frozen empty-root return and ONE against a failing output control; its product
stub panics if reached, so no field call is silently assumed. K101/K102
validate the exact KMX copy configuration for that unchanged source packet.
All these receipts are green before final promotion. Allocation
failure, physical carrier interpretation and the approved standard allocator
and semantic transport remain the existing root trust. There is no new
runtime syscall or cryptographic trust item. QueryGeometry::for_range and
query_loop remain OPEN even if this local root is promoted. No incoming
geometry-to-prefix edge is inferred from length arithmetic alone.

Allocator qualification: the named Allocator runtime trust is inherited from
the security contract (SECURITY-CONTRACT-20261021.md, owner amendment
2026-10-26, existing runtime items). This packet checks successful constructor
metadata and all nongrowing steps; it does not discharge allocator/abort
realization or add an allocator trust item. NativeContractSemanticTransport,
RootPhysicalInterpretation and Allocator are all retained explicitly.
