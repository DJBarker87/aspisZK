# Live authenticated relation observation

`lean/SameBodyLiveRelationObservation.lean` closes the byte/scalar seam at
the post-query relation boundary.  Its executable constructor uses the same
successful middle run to build the typed q22 schedule, runs the functional
opening pipeline on the same body, canonically encodes the resulting shifted
query scalar, and rejects unless those bytes equal the bytes consumed by the
chronological later-relation script.

The returned object retains both successful script traces, the canonical
same-body parse, the opening-pipeline success and the byte equality.  Thus the
equality is constructed by execution rather than accepted as a theorem
premise.  Canonical-body failure, opening-pipeline failure and byte mismatch
remain three distinct error results.

This is not yet complete verifier acceptance.  Construction of the concrete
OOD `Data` from the sampled points and body, the functional hash view, the
ordinary/image scalar and weights, the legal causal relation strategy,
terminal acceptance, Rust refinement, payment extraction and probability
coupling remain open source boundaries.

The focused Lean 4.32.0 NUC build used a user systemd scope with
`MemoryHigh=8G`, `MemoryMax=9G`, `MemorySwapMax=0` and a 600-second runtime
cap.  It exited zero in 7.41 seconds, used 6,760,856 KiB peak RSS and zero
swap.  Both promoted theorems use only `propext`, `Classical.choice` and
`Quot.sound`.  Full output and hashes are under
`results/v8-completion-fs-extraction-20260911/live-relation-observation-v1/`.

No protocol, proof-body, verifier-acceptance or security-ledger change is
made.
