# Function-contract shape fidelity

Pending full controls. Every row is provisional until its positive and matched negative results are checked. Kani0.67.0/CBMC6.8.0, fixed offline frozen graph and lock, KMX patch exact upstream.

Initial Result<u32,Error>:
- K010 identity proof_for_contract PASS; K011 inverted ensures FAIL.
- K012 weak contract PASS; K013 real caller PASS.
- K014 weak stub_verified caller COMPILE FAILURE: Error lacks Arbitrary. This is not the required logical FAIL.
- K015 undeclared modifies write FAIL.
- K016/K017 verified call-site installation/control COMPILE FAILURE for same missing trait.

No Result contract reliance is admitted from these initial runs. Repair only in own scratch harness: exhaustive generator for all eight frozen/default-feature Error variants. No variant/return is assumed successful. Option<M31> needs a field-crate cfg(kani)-only harness implementation of Arbitrary for public M31(u32), with all u32 values (no canonicality restriction). Slice-reference and Result<Vec<u64>,Error> shapes receive their own controls. These tests do not themselves establish a decoder, allocator, or complete caller bridge.
