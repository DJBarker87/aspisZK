# Element-loop copy replacements

Validated on cargo-kani 0.67.0 / CBMC 6.8.0: K008 has six expected-value
PASS results and six intended wrong-value FAIL results, with unwinding
assertions enabled. K005 independently validates the slice pair.
K007 is a compile failure corrected by preserving Vec's allocator parameter.

The patch contains three new files: `KMX_stubs.rs`, `KMX_native.rs` and
`KMX_CopyMeaning.lean`. Apply it in a scratch directory; place the Rust
module beside the scratch crate root and compile the Lean file separately.
Exact admitted validation commands are in K008, R002 and L003 receipts.

`KMX_stubs.rs` is a scratch module; declare it at the crate root. Enable
`#![feature(allocator_api)]` in that scratch crate (pinned nightly only).
Compile with `-Z unstable-options -Z stubbing`. Add all applicable attributes:

```rust
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
```

The generic entry is replaced across reached monomorphizations, not just u8.
Keep the original property and assumptions. Enable unwinding assertions;
allow at least the longest element loop **and** the largest reallocated byte
prefix, plus termination. Replacement of extension alone does not cover growth.
The growth pair in K008 installs both pointer-copy and realloc replacements.

R002 compares std and the final allocator-generic replacements using optimized
native Rust, across 1,466,538 checks: all 49 concrete configurations, exhaustive
lengths 0..6 over a five-value u32 alphabet and its type-specific images, all five
element types, destination offsets 0/1/3, four capacities, and seeded random
larger inputs (16 trials per type and length through 1768 elements). Realloc
comparisons include shrink, equal size, and growth and compare the retained
prefix. This is finite testing, not a universal Rust equivalence proof.

Preconditions: T is Copy (arbitrary Clone side effects are not modeled),
matching slice lengths, valid/aligned/nonoverlapping pointer regions, valid
allocator layouts, positive valid realloc size, and allocator ownership.
Realloc copies MaybeUninit bytes so spare capacity need not be initialized;
on allocation failure the old allocation is retained. No capacity, address,
allocation-count, or performance equality is claimed. The release properties
being rechecked concern values, not those observables.

`lean/KMX_CopyMeaning.lean` states indexed-copy, frame, append and retained
reallocation-prefix laws. L003 compiles with only propext, Classical.choice and
Quot.sound (append needs only propext). L001/L002 failed and have no proof
credit. This is a value-level specification, not a Rust-to-Lean refinement.
