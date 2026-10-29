# Pre-inline deployed array and slice indexing

The fresh 1.94.1 source capture identifies the exact scalar path:

- `core/src/array/mod.rs:401` `IndexMut::index_mut(self as &mut [T], index)`: unsize the same mutable loan, then delegate once.
- `core/src/slice/index.rs:30` `index.index_mut(self)`: delegate the same index and same mutable slice loan once.
- `core/src/slice/index.rs:276` usize `SliceIndex::index_mut`: `&mut (*slice)[self]`, explicitly documented in rust-src as intrinsic indexing. This is the compiler intrinsic boundary; there is no omitted Rust pointer loop in this selected body.
- `as_slice`/`as_mut_slice` return `self` under shared/mutable unsizing. They do not allocate, copy the backing elements, or invoke destructors.
- `slice::len` calls `ptr::metadata(self)`. The metadata source/intrinsic boundary must be named with V370, rather than treated as an additional Rust function body.

The non-scalar Range implementations in the capture are distinct bodies. They are not credited merely because the scalar path is bound. Error and abort behavior generated for intrinsic bounds checks remains at V370 / D381,D386; source caller range proofs are separate. No compiler obligation is removed.
