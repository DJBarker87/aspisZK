# Draft only — not validated

`KMX_copy_stubs.patch` adds standalone scratch sources, not shipped-code changes.
Do not use this patch to restore proof credit. K003 failed compilation because
stubbing was not enabled. K004 enabled `-Z stubbing` but the launcher failed
before invoking Kani. No stub has a completed Kani validation receipt here.

In a scratch module importing `alloc`, the drafted slice use is:

```rust
#[kani::proof]
#[kani::unwind(18)]
#[kani::stub(<[u32]>::copy_from_slice, KMX_copy_from_slice)]
fn example() { /* expected-value property and separate negative control */ }
```

Run with `-Z unstable-options -Z stubbing` and unwinding assertions enabled.
The pointer replacement requires valid aligned, initialized, nonoverlapping
regions. All replacements require `T: Copy`; the clone replacement does not
model arbitrary side-effecting `Clone`. Destination slice lengths must match.
Vector push can still reach allocator reallocation/copy paths: replacing only
`extend_from_slice` does not establish a reliable growth model. These paths
remain to be audited and validated before replaying release harnesses.

`KMX_native.rs.txt` drafts differential checks; it has not been executed.
`lean/KMX_CopyMeaning.lean` gives value-level loop specifications only and has
not been compiled. It is not a Rust-to-Lean refinement theorem.
