# R137: exact transcript external closure

Source base: `4ce8729f26658a944711da8c2a7fcfb1087807bc`.

R136 extracted the frozen selected callback's `before_ood` body, but its
imported `aspis-core` transcript type, five labels and five operations were
still external templates.  R137 separately extracts those exact operations
from the pinned `aspis-core` source and supplies the generated definitions to
the R136 callback overlay.

The extraction-only crate differs from the pinned crate only by six public
reachability wrappers in `lib.rs`.  The pinned `field.rs` and `transcript.rs`
are byte-identical to the R136 source pins.  Charon extraction and Aeneas
translation completed under the recorded 5G/7G, zero-swap scopes.  The raw
generated R137 overlay contains concrete definitions for transcript creation,
absorption, squeeze, QM31 rejection sampling, nonzero retry, QM31 byte writing
and the five labels; it contains no external axioms.

The integration overlay maps the structurally identical R136 field values to
the R137 values, aliases the R136 transcript type to the exact R137 type, and
implements every former R136 external through the extracted R137 definition.
All six focused Lean targets compile.  The two field conversion round trips
depend on no axioms.

This closes the *implementation* gap in R136's generated callback overlay.  It
does not yet prove that the generated callback execution equals the pure
selected-schedule model.  The first remaining source-specific proposition is
an exact byte-address/state bridge for `Transcript.new` and both packed and
long `Transcript.absorb` branches, followed by the QM31/nonzero sampler
result-and-state bridge.  Actual sampler admissibility, privacy and soundness
remain open.  No verifier source changed and the measured endpoint remains
**999,790 / 999,532 CU**.

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r137_evidence.py
```
