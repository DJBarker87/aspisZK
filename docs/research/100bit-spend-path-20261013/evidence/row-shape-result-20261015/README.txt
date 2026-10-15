Focused exact-source row_shape proof receipts (Lean4.31).

Final source is lean/ExtractedRowShape.lean, SHA pinned in provenance.json.
all-rows-b exits0 and audits all8 public theorems with only propext,
Classical.choice and Quot.sound. Source, exact command, imported generated
source/object hashes, wall time, aggregate RSS sample, process RSS/swaps,
and system swap readings are retained. No compiled binary is committed.

arithmetic-a failed on an ambiguous dite_true name and redundant proof tail;
arithmetic-b fixes those and passes the generic arithmetic predecessor.
all-rows-a passes range>=27 but fails missing IntervalCases tactic import.
Its failed declarations report sorryAx because elaboration failed; they are
not release results. all-rows-b adds the existing cached tactic import and
passes the complete table and exact None interval. No unchanged rerun.

Runner uses lake env lean through a cache-path wrapper, reads coordinator
Types/Funs objects, and writes only worker output. Four GiB process-group RSS
stop plus Lean-M3500; no package/cold dependency build, host, or installation.
The runner snapshot retains original locations to reproduce the actual
command; relocate paths explicitly when replaying elsewhere. Proof is about
the extracted declaration; Rust refinement and parser/prefix closure remain
OPEN, as does the main project Lean4.32 dependency boundary.
