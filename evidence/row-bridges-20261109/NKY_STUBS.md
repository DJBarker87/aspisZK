# NKY stub inventory

No new field-operation stub, multiplication proof or extraction is used.
TX1:235 inherits NKI_STUBS.md and the CLOSED234/field laws already admitted by
NKW; those dependencies remain pinned. No XRn join/stand-in is used.

The native Box harnesses replace only the raw decoder child with a local-free,
readonly oracle returning an arbitrary FULL typed Rust Result, including every
raw error variant. Checkpoint maps to CLOSED152, master to CLOSED153. The Lean
instantiation is NKF_CheckpointBox.source / NKF_MasterBox.source at the SAME
bytes and NJQ decoder cut, through NKY_BoxTotal.checkpoint/master. No child
output is assumed successful. The body after that child does not read bytes;
1is a native harness allocation extent, not a length restriction. The inherited
NKP_BoxUniformity laws and exact frozen body establish this uniformity.

Copy uses exactly the KMX_copy_stubs.patch configuration, SHA256
bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
No authored copy stub. Every credited native family has its matched failing
controls in that configuration. Native frame K014's whole-struct memcmp is
excluded and replaced by the typed coordinate/window family K015..K020.

Box::new itself is executed natively, never stubbed. Returning allocation is
Kani's Box model under (aa). Fresh ownership or abort is the existing Allocator
item; no recoverable allocation error is introduced. The arbitrary Reservation
at the sole source site is handled in Lean: Err aborts, allocator fail/div
propagates, returning Ok uses that invocation's captured carrier and post.
`events` is a pure projection of the SAME allocator action in `native/run`,
not an additional source allocation. On nonreturning arms the observed carrier
is an unused ghost and no returning window is required.

No proof_for_contract/stub_verified, Option<fn>-dependent observation, writable
static, RuntimeCpiReadonlyEntry7 or new runtime trust row is used.
