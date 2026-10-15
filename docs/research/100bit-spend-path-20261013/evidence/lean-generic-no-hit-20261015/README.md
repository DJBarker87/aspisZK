# Generic no-hit evidence

This focused Lean target proves generic list bookkeeping: `hitFrom_append`, `doomed_ext_bad`, and a noncomputable witness selector characterization. It preserves the explicit bad predicate and witness relation; it does not instantiate a protocol relation or prove a probability/security bound.

Attempt `a` failed with proof errors and emitted five axiom reports, including `sorryAx` in two reports. Attempt `b` is the successful final source with five standard axiom reports (`propext`, `Classical.choice`, `Quot.sound`). Both attempts are retained byte-for-byte.

The build used the pinned Lean 4.32.0 environment and the 4G high / 6G max / 0 swap cgroup recorded in each receipt. See `source-manifest.json` for source, direct-import, object, runner, and receipt hashes.
