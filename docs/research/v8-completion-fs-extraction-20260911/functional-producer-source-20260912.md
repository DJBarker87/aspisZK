# Source-driven compact functional producer

`SameBodyFunctionalProducerSource.fromInputs` parses the canonical same body,
constructs checked sampled OOD data, executes the repaired ordinary
row/interpolant/public correction, and returns the compact public functional
description and claim.  Its retained theorems establish:

- exact provenance through `fromSampled`, fixed-field parsing and `correct`;
- `Data.Checked` and `data.gamma = gamma`;
- a 545-byte description and canonical 16-byte claim.

`check_functional_producer_source.py` compares the frozen Lean constants and
layout against the pinned `structured_weights.rs` and selected Rust constants.
It checks the 43-byte prefix, six metadata bytes, 64 group indices, seven
masks, 128 generated u16-LE bytes, concatenation order and total length.  This
is a fail-closed source/layout diagnostic, not a Rust refinement proof.

The public statement point `z` remains an explicit source boundary.  More
importantly, the existing `FunctionalProducer` interface is total while the
real constructor may reject.  Integration must therefore add a source-shaped
rejecting branch to the research script; arbitrary fallback bytes would be an
invalid repair.

Focused NUC Lean compile: exit 0, wall 3.05 seconds, peak RSS 6,765,832 KiB,
swap 0, with only `propext`, `Classical.choice` and `Quot.sound`.  Source hash
`f62cdffda826f9a9823588de0be04886756813fcadd0a3a5711366d0e8f948fa` and OLean
hash `8ee33570b51f8d400ec1772f02a3279823f02826a3d739547f4549967658209d`.
Dependencies were cache-reused, not rebuilt.

Local checker command:

```text
python3 docs/research/v8-completion-fs-extraction-20260911/check_functional_producer_source.py
```

It passed with script hash
`493dea14d93599e88224357ae7753ffb2673e1522bb99fdd44764d6ad3609ec6`.
