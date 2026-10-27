# Stable mathematical instance

Published declaration: `R1Z.ProverRw21ModelInstance` in
`R1Z/ProverRw21ModelInstance.lean`.

The function serializes mathematical `ProverRw21ProtocolOutput.Transcript`
data (exact field elements and digests), through the independent reference
serializer, preserving preparation errors, failure and divergence.
No actual-source output defines its arguments or result. The data structures
contain no refinement/equality proof fields. Source callbacks do not define
these mathematical values. The byte layout is S2, matching the existing
`ProverCommitFront46` model's fixed header.

**This is not yet the requested concrete deployed-input-to-model function.**
The mathematical protocol construction from deployed caller inputs remains
open. Join consumers can import this stable serialization instance read-only;
they must not claim it discharges that missing construction, the fixture byte
equations, or V163. Existing published statements remain unchanged.

Checks: attempt 37702 ProtocolOutput, 37703 ModelInstance, both exit 0,
standard axioms only; per-attempt JSON and full logs record metrics/pins.
Attempt 37701 is the retained failed bounds-proof script, corrected before
publication. No unchanged failure was replayed.
