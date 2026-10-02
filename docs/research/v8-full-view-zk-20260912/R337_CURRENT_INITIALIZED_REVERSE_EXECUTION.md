# R337: initialized prefixes feed both actual reverse loops

`AspisV8R19/R337InitializedReverseExecution.lean` compiled successfully. Both actual initialized prefix fragments establish the prefix reads consumed by their actual reverse loops. The first composes R332 with R311 loop2; the second composes R336 with the body-identical loop3 bridge. Canonical source reads, nonempty source length, exact iterator start/end and initial output length remain explicit. All remaining-count, prefix-read and output-index bounds follow from these conditions. Arbitrary encoded accumulator and zero input/products are allowed; no separate nonzero/success/capacity premise is added. This is not a proof of original caller guards, inverse seed selection or output allocation/setup, independent compiler/standard-library correspondence, or complete batch execution.

Compile revision `37d5dd7ecb2c6f7b98822147522b043884ef77d9`; exit 0; wall 0:01.71; child peak RSS 3719608 KiB; swaps 0. Both complete axiom reports use only propext, Classical.choice and Quot.sound; no sorryAx, native proof or new execution assumption. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r337-current-initialized-reverse-execution/manifest.json).

First remaining proposition: Prove the exact source allocation/range/index-zero output setup and bind actual shared inverse seeds to these derived prefix/reverse invariants. Prove original source traversal guards and complete callback/error/oracle chronology, then joint privacy and soundness.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
