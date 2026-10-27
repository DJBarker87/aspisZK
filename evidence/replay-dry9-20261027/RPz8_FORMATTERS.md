# Fresh Rc10 formatter reachability

RPz8_360 succeeds: 11.226724941981956 s (exact receipt authoritative), peak RSS
5,865,656 KiB, zero swaps, fixed 6G/8G/Swap0/Tasks64 scope, Lean -M7000.
`AspisR1.Rc10_Top.deployed` has only propext, Classical.choice and Quot.sound.

All **180/180 formatter records are present** in the fresh root environment.
All **180/180 are unreachable** from the root's kernel dependency closure.
Every record has a Boolean result; none is unknown/null.
`RPz8_Rc10_Top-formatter-records.json` contains the complete per-record table.
The raw query and full printed axioms are in RPz8_360/stdout.log.

The checked meta query starts with the deployed theorem, visits its complete
kernel type and value, including opaque/theorem values, and recursively visits
the constants returned by the pinned Lean `Expr.getUsedConstants`. Inductive
constructors are added explicitly, as in Lean's axiom dependency collector.
Every visited constant must exist in the checked kernel environment; otherwise
the query throws an error instead of assigning negative results. The traversal
completes with **104,783** distinct constants, retained in
`RPz8_Rc10_Top-reachable-constants.json`. Types and proof bodies are inspected;
no large concrete term is normalized.

Each formatter record is queried against that completed visited set. Constant
parent paths and owner paths would be emitted for positive results; none occurs.
No positive import-path witness is therefore required. The complete imported
module headers remain in the raw log. Import presence alone is not treated as
proof-term reachability, and partial-context absence is not used as evidence.

The retained corpus contains the 180 historical formatter records. Its list of 85 historical nonstandard names classifies freshly as 84 actual native formatter axioms plus the definition Formatter := Unit. The pure definition is reachable; all 84 actual axioms are unreachable. RPz8_FORMATTER-CLASSIFICATION.md records both exact paths and uncached standard-only root audits. The all-declaration standard-only gate remains false for the retained corpus. No generated formatter or
shared pure matcher is deleted, edited or silently substituted.
