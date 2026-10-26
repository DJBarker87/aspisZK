# Focused source-law preflight

The next consumer of op258's extracted function is `PV_CB3_Op258Source.op258_source`.
`PV_CB3_PoleRows` is a generic Boolean helper only, not the source equation.
No concrete recurrence evaluation or large finite-type enumeration is required.
No maxHeartbeats/maxRecDepth overrides are introduced. Sources remain uncompiled
until a permitted focused run; no source closure is claimed from this file.

The shipped loop visits every row and operand, even after `clear = false`.
For arbitrary slice lengths it may panic at the first mask lookup beyond index 63
(row 1024). Its complete Result equation must preserve that failure; totality
under `values.len <= 1024` would be a separate conditional helper theorem.
The planned `pole_rows2` Kani harness is a tiny preflight, not a sufficient bound
for the full function, and is never credited as a row closure.

Local Lean is installed, but this worktree has no local Mathlib/Aeneas cache.
Do not start a cold dependency build to work around host contention. The standard
Env-J launcher can compile the generic `Std`-only helper independently.
