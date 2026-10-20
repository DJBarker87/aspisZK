# Powers callback exact field product

PROVED: the emitted callback from the unchanged powers source is total on canonical state and challenge inputs; it returns the prior accumulator, preserves the challenge, and updates the accumulator to a canonical representation of their exact degree-eight field product. The successful-call theorem states the same result without assuming a separate multiplication law.

The selected callback's concrete multiplication instance is connected to the fully extracted, no-opaque current WideExact::mul graph by checked coordinate maps and the source-graph result equality. Its field meaning comes from the already proved total/canonical/exact Wide product theorem. This reuses existing arithmetic and callback proof objects without replay.

Frozen source: b2727acd3, according to LEAD-FREEZE-20261020.md. The three relevant whole files are byte-identical to this freeze; hashes are recorded. No production change, source migration, resource option override, custom axiom, or binary is included.

One focused NUC target: exit0, 1.907 seconds, process peak RSS 3,695,352 KiB, cgroup peak 371,843,072 bytes, swap0, no cap events. Six axiom reports: one has no axioms; five use only propext, Classical.choice, Quot.sound. Compiler/source/object/import pins and command are recorded, with -M4400, MemoryHigh1GiB/MemoryMax2GiB/MemorySwapMax0. Shared mapped imports explain RSS versus cgroup accounting.

OPEN: whole powers-array traversal, original borrowing from_fn interface and Rust-library correspondence, current Prepared caller refinement, upstream canonical sampler invariants, runtime/ELF refinement, and cryptographic theorem composition. This is an exact source-callback arithmetic result, not a whole powers or 100-bit theorem.
