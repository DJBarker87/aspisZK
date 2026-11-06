# Owned input repairs

Before submission, the native runner's predecessor-prefix replacement and missing
local input-store directory were corrected. Neither launched a scope.
NKY_K001 exited 1 in validation before Kani: the base source seed lacked KMX files.
NKY_native_seed copied the retained predecessor source read-only into the own
workspace; every imported file hash is retained. The strict validators are
unchanged in meaning. NKY_K002 passed with the same harness name/property.
No timeout or memory-killed shape has been replayed.

NKY_L019 stopped before a scope: its changed dependency NKY_LevelsLoop had
not yet compiled. No process was submitted. NKY_L034 scanner honestly exited1
because the authored expected-import table omitted implicit Init. The strict
matcher was unchanged; the source-based manifest parser now includes Lean's
implicit Init. Final scan is on the changed final combined source, not an
unchanged regression. NKY_K014 full-struct equality failed builtin memcmp
unwinding at35; it was replaced by an arbitrary typed field/coordinate window
under the SAME harness names, not rerun or given more unwind/time/memory.

L073 rejected the reserved Lean identifier `at` in the new field-observer
proof; it was corrected to `readImage` before changed L074. L079's strict
export check refused to overwrite the first immutable export's old combined
object after the additive post-heap extension. No old cache was overwritten
or deleted. The OWN export destination was changed to NKY_exports_final_20261109;
the same exact hash/provenance checks are retained, and L080 performs focused
statement review plus that final pin/export. No cap, timeout or budget changed.
