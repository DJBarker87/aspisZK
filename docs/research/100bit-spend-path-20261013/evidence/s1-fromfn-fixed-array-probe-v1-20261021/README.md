# Candidate-only explicit powers extraction probe

This packet tests whether replacing the `weights::powers` call to `core::array::from_fn` with an initialized `Copy` array and an explicit bounded `while` loop gives Charon/Aeneas a usable body. It is a feasibility probe for a reviewable candidate; it does not change the frozen verifier or establish Rust standard-library equivalence.

The retained replacement to consider is the exact generic candidate in `lean-candidates/s1-explicit-loop-powers-proved-candidate-20261020/extraction-input/lib.rs`. Its source checker passes, and its Lean owner `LoopPowersCandidateTotal.powers_total_exact` proves, for every length `N` and canonical input `x`, termination, canonical outputs, and entry `j` decoding to `x^j`. The proof uses the pinned current field backend. The replacement initializes `out` before `p`, writes `out[i] = p`, multiplies `p` by `x`, and advances `i` until `N`.

The new isolated N=29 extraction in `generated/` successfully emits a nonempty `weights.powers_loop.body` with the expected update, multiplication and cursor step, and no `from_fn`/`try_from_fn` call in generated `Funs.lean`. This extraction probe placed `p` before `out`; its generated state tuple is therefore `(p, out, i)`, unlike the proved generic candidate's `(out, p, i)`. The probe does not prove these Lean constants definitionally equal. It is corroborating evidence that the candidate shape extracts, not a new Lean theorem or substitute proof owner.

The candidate source pins retain the field structs/constants and `WideExact.mul` dependency from extraction input revision `d8cb8b0081f55a6a3d63f0f34ab790082f8d0ad0`; multiplication is the explicit opaque child in the extraction invocation. The proved generic candidate packet separately records the inverse coordinate maps to the concrete current `WideExact` arithmetic owner. Compare those pinned source cuts and owner hashes when preparing a new extraction/re-pin; this probe by itself does not bind its newly generated namespace to the generic theorem.

## Extraction result

- Charon and Aeneas both exited 0 using the pinned binaries recorded in each `receipts/*/receipt.json`.
- Charon: 0.201 s, process peak RSS 145,024 KiB, swap 0.
- Aeneas: 0.402 s, process peak RSS 65,120 KiB, swap 0.
- Both ran with MemoryHigh 2 GiB, MemoryMax 3 GiB, MemorySwapMax 0; no cap or OOM events.
- The generated Funs SHA256 is `d4de1ffa5472c677c5457c45ff636a8b78de2024e5fece196774e5762754094a`; LLBC SHA256 is `e745845c35d3b3fb226483dd8391bb5160a67d00eaea452d826bc957a38f8f18`.

Run `python3 check-probe.py` to validate the pinned probe inputs, generated body shape, absence of std `from_fn` in the generated functions, and successful capped extraction receipts. The checker deliberately does not claim a Lean proof for this new monomorphized output.

## Review and adoption boundary

Proposed review option: replace only `weights::powers` with the retained out-before-p generic candidate body. The existing generic Lean proof is the mathematical owner; this packet supplies extraction feasibility for the same loop algorithm. Production remains unchanged pending lead review and an explicit new source freeze.

Still open: establish a source-to-generated correspondence for the exact adopted ordering and current call sites; connect the chosen helper to its caller and re-pin every affected declaration/object; verify the relevant Rust `from_fn` behavior or eliminate that library boundary through the adopted helper; measure optimized SBF/ELF and per-fixture CU/runtime effects; and pass the lead's adoption/frozen-order gates. No CU saving or budget compliance is claimed here. Prior candidate CU results in the generic candidate packet include over-budget variants and must not be transferred to this exact helper without measurement.
