# Stage 1: checkpoint weights traversal and carrier fold

Checkpoint remains OPEN; prepared_claim has not started. No headline premise removed.

LPm_K001 universally checks one actual `Accumulator.weights` Vec iterator.next
from every suffix i=0..64 of arbitrary 64 four-word fields: head values, exhaustion,
all remaining fields by arbitrary coordinate, retained Vec length, covers at 0/63/64.
Unused accumulator fields are arbitrary next and zero rhs/power carrier fillers;
the selected source partition reads only weights. No result for other fields is inferred.

LPm_K002 joined the full iterator carrier and arbitrary-prefix writer and timed out
at the unchanged 90-second harness limit. It is excluded and never rerun. The
replacement is a split: K001 supplies the selected shared reference and tail;
LPm_K003 checks the frozen shared-pattern dereference and native put_k continuation
on EVERY arbitrary 712+16*i-byte prefix, i<64. All prior bytes, all 16 written bytes,
and the length are checked by arbitrary output coordinate. The paired QM31 writer
stub is LPi_contracts::qbytes / LPi_WriterValues.qm_writer (raw U32s, exact16 slice).
No stronger canonicality precondition is added. Own TMPDIR had no retained solver
files after K002 (read-only find returned no entries).

LPm_WeightLoop.Trace records remaining fields and linked successive Vec states;
each constructor has only a LOCAL put_k append equation. `result` derives the
whole fold, `native_weights` uses the SAME actual Accumulator.weights and inherited
LPi_SerializationFold.weights64 to obtain every byte and length1736 from length712.
`reached_size` and `reached_domain` establish every next local prefix falls inside
the passing native writer domain. `exists_trace` supplies local consistency on every
raw field/list, rather than relying on a fixture. Native trace association uses
K001/K003 for every iteration plus the exact frozen for-pattern/source partition;
it is the hybrid P6 route, not an assertion that Lean elaborates Rust.

Validation: LPm_L001/L002 privately rebuild unchanged missing LPi objects against
SInt2; no old theorem re-proved. LPm_L004 compiles the new loop module; all five
printed theorems have only propext/Classical.choice/Quot.sound. L003 rejected
reserved-word binder names and is excluded in full. K001 exit0, wall83.176s,
RSS5345908KiB, swap0; K003 exit0, wall28.768s, RSS1070292KiB, swap0. Exact
source revision/hashes, dependency/tool pins, commands, scope limits and full
outputs are in the attempt receipts. Every admission had exit0 AND allowed:true.
All3 Kani runs have fresh exact frozen graph/edge audits, offline execution and
unchanged frozen Cargo.lock. All498 frozen corpus files match after removing
ONLY the explicitly listed cfg(kani) registrations. Repository crates/programs
are unchanged. Historical ELF pins remain inherited; no rebuild trigger fired.

This stage does not close the same-execution whole checkpoint serializer/digest
join. Next: finish source-shaped body/model program and audit concrete native
field/append association; do not promote a model program equality to native closure.
