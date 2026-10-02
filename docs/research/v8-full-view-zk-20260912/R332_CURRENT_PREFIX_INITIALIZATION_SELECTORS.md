# R332: actual initialized prefix reads and final product

`AspisV8R19/R332PrefixInitializationSelectors.lean` compiled successfully. The selected first-vector source initialization establishes the exact original input length, every canonical encoded sequential prefix product, and the final product. The complete emitted Slice.last read on Vec.deref returns that encoded final product. These results derive from R329 under its explicit nonempty/canonical-source-read conditions; capacity is derived and zero products are permitted. Algebra/list selector lemmas separately state their exact output-equation premise. No full batch guard, second-vector initialization, nonzero total, inverse, independent Rust-library/compiler correspondence or whole callback result is claimed.

Compile revision `86706bd4cc5aa6d51cf36828d6c049af8202a403`; exit 0; wall 0:01.62; child peak RSS 3712452 KiB; swaps 0. All five complete axiom reports use only propext, Classical.choice and Quot.sound; no sorryAx, native proof or new execution assumption. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r332-current-prefix-initialization-selectors/manifest.json).

First remaining proposition: Use these derived prefix selectors for the reverse-loop invariants and prove the source batch guard, both vector initializations and total inverse/output setup. Resolve actual source traversal/fold/extend and compiler frontiers, then complete full callback chronology, universal joint privacy, shared-oracle/seed/publication simulation/losses and soundness.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
