# Mutable Enumerate projection and write-back bridge

This source-only addendum records the focused Lean bridge for the generated `iter_mut().enumerate()` adapter. The theorem proves that erasing the Aeneas write-back continuation from `IteratorEnumerateMut.nextWithBack` yields the generic `IteratorEnumerate.next` step for the selected mutable-slice iterator instance. A second theorem proves that, on successful `nextWithBack`, the continuation routes the replacement value to the inner `IteratorIterMut.next` back callback (and supplies `none` when the inner iterator returned no item).

The pinned Aeneas model source is included. In `SliceIter.lean`, `IterMut` is marked `body := .opaque`, while the handwritten `IteratorIterMut.next` and `Slice.iter_mut` definitions specify the model used by the Lean proof. `Core/Iter.lean` defines the generic enumerate counter behavior. This addendum proves the custom generated adapter is consistent with those selected Aeneas definitions; it does not prove Rust's unsafe slice-iterator pointer/borrow implementation refines the opaque `IterMut` model. NUC's installed stable rustc is 1.94.1 (`e408947bfd200af42db322daf0fadfe7e26d3bd1`), but the `rust-src` component is not installed, so the exact Rust stdlib source body was not available in the extraction workspace. Treat that Rust-to-Aeneas `IterMut` refinement as the remaining semantic boundary.

## Lean source and result

- Module: `BwFinishEnumerateMutCorrespondence`
- Source: `sources/BwFinishEnumerateMutCorrespondence-v11.lean`
- Source SHA-256: `e59bf2a81383a7f5c1840befea135ee6244c6f0891d6db2b877f4998a1f9f5b74`
- OLean SHA-256: `6669e0690c65a40f1cbd9f4919b60b94bc839a6df414185e6dc9ebe26caddff4` (hash only; no binary is included)
- Result: exit 0, 1.405 s, peak process RSS 2,643,876 KiB, scope peak 300,093,440 bytes, scope/process swap 0.
- Both theorem axiom reports: `[propext, Classical.choice, Quot.sound]`.
- Attempt evidence: `evidence/lean/` retains exact command, preflight, receipt, Lean log, and `time.log`.

## Pinned Aeneas source

The selected Aeneas source checkout was `aeneas-circle-joinfix-b59-20261019`, git commit `b59d5188c082f704a418c7cb4e52ad69328002d1`. The two source files and their hashes are retained under `aeneas-source/`. The checkout had unrelated modified interpreter files at inspection time; neither pinned source file was modified.
