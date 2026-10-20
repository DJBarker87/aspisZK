# Powers invariant and direct library-extraction frontier

PROVED: assuming the current callback accumulator decodes to x^n and its inputs are canonical, successful execution of the unchanged emitted callback returns a canonical x^n and advances the canonical accumulator to x^(n+1). It derives this from the preceding concrete full-source multiplication theorem. This is the invariant required by an eventual whole-array traversal proof; no traversal correspondence is assumed proved here.

Focused target CurrentPowersCallbackInvariant: exit0, 2.207 seconds, process peak RSS 3,689,572 KiB, cgroup peak 368,742,400 bytes, swap0, no cap events, standard axioms only. Pinned Lean4.32, -M4400, MemoryHigh1GiB/MemoryMax2GiB/MemorySwapMax0; no repeated dependency replay.

The direct Rust-library route was tested on the unchanged original powers cut with opaque multiplication. These are DIAGNOSTICS, NOT accepted Lean sources:

- Explicitly including core::array::from_fn succeeds in Charon and Aeneas and emits its real wrapper body, delegating to try_from_fn. This does not solve the original borrowed FnMut ABI mismatch or close the library boundary.
- Including try_from_fn and try-trait bodies succeeds in Charon; extended-static Aeneas exits2 at Rust core array/mod.rs:155 with “Can't copy a mutable borrow” (InterpExpressions.ml:227).
- Reusing the same LLBC with the alternate pinned Aeneas also exits2 at the same mutable-borrow frontier. The retained Charon receipt is reused, not claimed rerun.
- Monomorphizing and including try_from_fn_erased succeeds in Charon; extended-static Aeneas exits2 during TypesAnalysis.ml:229 for the core array Guard type at array/mod.rs:934.

Every attempt used MemoryHigh2GiB/MemoryMax3GiB/MemorySwapMax0; no OOM or cap increase. Exact commands, source cuts, tool hashes, LLBC hashes, status/timing/RSS and logs are retained without LLBCs or compiled binaries. A resource-admission denial preceded v1; no compiler ran in that rejected admission. Failed translation outputs and raw generated external axiom/resource-option templates are diagnostics only and are not imported by the proof.

Frozen source remains b2727acd3. No production changes or adoption. OPEN: Rust-library correspondence and borrowing-interface lowering, the full powers-array owner, Prepared/weights caller links, input reachability and runtime refinement, and complete 100-bit composition. The owned-closure candidate is separately recorded under lean-candidates/s1-powers-owned-closure-diagnostic-20261020; it is not part of the frozen implementation.
