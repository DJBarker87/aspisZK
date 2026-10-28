# NCK substitutions and domains

No field operation is stubbed or proved in Kani in this lane. No new field
multiplication theorem, arbitrary-success callee, SHA model, function contract,
proof_for_contract or stub_verified use is introduced. Consequently the field
(stub, emitted-ok Lean theorem, canonical domain) table is empty. Caller-level
native arithmetic/contract composition remains OPEN, not credited by omission.

| Substitution | Value laws / source | Domain / calibration |
|---|---|---|
| core::ptr::copy_nonoverlapping → exact KMX_copy_nonoverlapping | mandated KMX_copy_stubs.patch; retained KMX_CopyMeaning.loop_spec/copy_prefix/copy_frame | valid allocated non-overlapping regions and initialized Copy values remain caller obligations; NCK_K002 false-copy control FAILS, NCK_K003 positive control PASSES |

The KMX file is included verbatim under NCK_kmx, never reimplemented or edited.
Patch SHA256:bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
Existing KMX value lemmas are reused, not claimed as a newly proved Rust memory
refinement. No whole release buffer copy is unwound for proof credit. New
snapshot gates cover only rejected-length/borrow-conflict branches; they do
not install to_vec on production-sized accounts. No digest VALUE is computed
or assumed beyond the existing runtime trust row; no syscall gate is claimed.

Option<fn>-dependent accepted-path gates are not claimed. Early-rejection
gates stop before observer construction/mark and do not depend on a function
pointer. No K-2 ruling is lifted by this work. Any future native accepted-path
bridge must satisfy that quarantine and all required matched shape controls.
