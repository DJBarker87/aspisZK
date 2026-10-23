# Owned adapter Stage 3

Branch `codex/cx-adapter-rw-20261023`; resumed from `b94f86c9ca`.
Candidate source is Stage 2's shipped owned implementation at `572236f37d`.
This report is in progress. Native Required14 and release target remain open
until the concrete obligations below are discharged. No adoption or push.

## Extraction and trust boundary

Charon004 and Aeneas003 extract both complete owned callers from the actual
candidate source, including owned ASQ8 authentication, registry admission and
reconstruction control. They do not extract a handwritten caller copy.
`generated-v3` retains the successful emission. Its old TypesExternal template
is a stale file from an earlier attempt: Types imports no external types, and
contains both enum layouts. It is not an input to the adapted model.

`AdapterRwTypes` / `AdapterRwModel` use the existing named-discriminant adapter,
remove generated resource settings, and replace 59 external operations with an
explicit `Ops` parameter. No operation is installed merely by parameterization.
Aeneas clipped one deeply nested registry tail's indentation at column68;
`repair_layout.py` repairs whitespace with checked non-whitespace token equality.
`adapt_extract.py` preserves the emitted branches, calls, argument order and
error mapping, and records raw/adapted hashes and all operation names.

Lean002 (types) and005 (whole model) pass on the capped host. Attempts003/004
are retained formatting failures, with recovery `sorryAx` excluded from evidence.
All successful model audits contain only standard Lean axioms. SDK snapshot and
write wrappers are outside this extraction, as designed. Runtime admission,
allocator behavior, child effects and source-to-SBF interpretation remain explicit.
