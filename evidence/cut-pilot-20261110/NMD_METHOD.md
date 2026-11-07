# NMD native cut-point method pilot

Target not yet established. Baseline ledger23: 580 CLOSED / 0 QUALIFIED / 19 OPEN.

Stage 1 tests pinned Kani 0.67 contract fidelity before any actual-child substitution: Result<Box>, Ref, RefMut, ProgramResult and plain Result. Each shape requires inverted-ensures failure, real-body pass versus stub_verified failure for an unimplied assertion, and detection of a modifies violation. No verdict yet.

Route A is gated on all controls for the exact interface. Route B is attempted only for a failing shape and uses local records reachable through existing arguments with the remaining complete footprint havocked. Writable statics and zero-content parent carriers are forbidden. No binding template is validated yet.

Stages: controls; actual parse/marker/common contracts and arbitrary-content parent; conditional local-record route; informational newest-Kani K-3 check; Lean segment fold and combined audit. Only CLOSED or gated candidate children may compose. Root0/1880 remain TX2:241 caller clauses. No new trust rows.
