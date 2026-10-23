# S9 constructor Box::new v2 SBF stack gate

This focused optimized SBF build tests the constructor-only source candidate that moves the final aggregate packing into `#[inline(never)] Weights::box_from_parts`. The candidate’s former `Weights::new` stack diagnostic is gone: a side-by-side comparison against v1 shows 35 diagnostics in v1 and 34 in v2, with all 34 remaining function diagnostics unchanged and no additions. The retained optimized rlib disassembly and relocation show that `Weights::new` reaches the out-of-line helper. Neither function appears in the v2 compiler stack diagnostics.

The build itself exited 0, but the whole-program stack gate remains failed because of 34 unrelated over-limit functions. The ELF and rlib are not included; only their hashes and selected disassembly/relocation audit are recorded. This packet does not report fixtures, compute units, or proof results.

The candidate changes allocator-failure behavior: `Box::new` aborts where the existing API returns `Error::Allocation`. This is not byte-equivalence; only successful-run refinement is in scope. The source snapshot used tracked revision `e668ce58d31bde2fe25d8c6e76eba2262fad9e96`, with the candidate source as the sole Rust source override.

Run `python3 check_packet.py` to verify the source/build/audit pins and enforce the split candidate-vs-whole-program result.
