# Owned powers closure: extraction diagnostic only

CANDIDATE, NOT ADOPTED. This isolated kit changes the unchanged powers source cut by adding `move` to its `core::array::from_fn` closure. Both captured field elements are owned. Production source was not changed. The verifier is now frozen at b2727acd3 (LEAD-FREEZE-20261020.md); this candidate is not a proof or re-pin against that freeze.

Measured extraction evidence: the pinned Charon succeeds in 0.201 s and pinned extended-static Aeneas in 0.402 s, with MemoryHigh2GiB/MemoryMax3GiB/MemorySwapMax0 and no memory pressure events. LLBC SHA256 21622433ed1b9efd925331d1c47a39a79fc9074adc3f4af3812acc003788a464. Multiplication remains an explicit opaque child, exactly as in the original callback extraction.

The emitted owned closure has a two-component FnMut call result `(value, state)`, and the emitted powers owner returns the array directly. This eliminates the two interface-shape mismatches observed in the original borrowed closure: its FnMut result had a third backward-function component, and its owner expected an array/state pair from an external template returning only an array. The raw generated text is retained as diagnostic evidence; its external axiom templates and resource options are NOT accepted Lean sources and were not compiled.

OPEN: typing the complete owned candidate with a concrete library model; exact output and old/new source equivalence; stdlib correspondence; all source/ELF/CU and freeze approval required for any adoption. No production adoption is proposed by this packet. The frozen-source route continues with the original emitted callback and investigation of direct core::array::from_fn extraction.
