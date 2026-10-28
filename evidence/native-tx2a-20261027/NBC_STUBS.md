# NBC replacement inventory

No `kani::stub` replacement is installed in K001–K003. No field multiplication
or dot arithmetic is executed as a proof gate. The cfg(kani) Arbitrary impl
constructs eight independent u32 fields directly inside the private WideExact
owner; it asserts no arithmetic fact and does not call U01 functions. Its only
consumer is the release no-op trace call. The domain includes all canonical
native values and extra noncanonical raw carriers.

`sourceDigest`, `digestOps`, `errorValue`, `errorOps` are explicit Lean model
constructions, not Kani stubs or evidence that the adopted dictionary contains
them. They receive no native closure credit. No LPh stub pairing is newly used
or introduced. Runtime, SDK, SHA256 and allocator trust items remain explicit.
