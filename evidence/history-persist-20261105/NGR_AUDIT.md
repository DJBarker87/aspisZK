# Combined validation

NGK_COMBINED_IMPORT + NGC writer + NGR proofs load together (L016). Every new
top theorem has printed standard axioms. L020 prints both full final binder
types under pp.all. Raw ax2 L018 covers all eight new top theorems, the headline,
NGC return/program identities, and CPH protection/trace/recorder:14 roots,
standard only, all equal collectAxioms, zero unresolved. L017 reproduces all8
planted/mutated fixtures in the SAME binary used by L018/L019. Walker bytes
match NEP_WALKER exactly; driver diffs only change module/root/manifest names.

NFX-method scan L019:13,441 modules;689,694 declarations;24,442,408 references;
zero dangling, incompatible owners or import mismatches;1,583 compatible cached
replicas disclosed. New source import baselines are independent source headers;
predecessor baseline is the committed NGP manifest with recorded NGK provenance.
NGR_validate.py verifies source snapshots, caps/admission, final compile source,
raw root/fixture outcomes, binary identity, closure SHA and source/import identity;
five mutations (dangling/owner/import/Init/axiom) are rejected.

Pinning: actual closure30,034 files/7,608,181,856 bytes; NGR_CLOSURE_PINS.json.xz
and raw SHA. All30,029 shared NGP files match;4 unrelated NGP modules are absent
from this target closure, not missing dependencies. Relative to NGK,30,012 files
match and5 .olean hashes differ. L023 raw-reads the five old/new modules using
Lean's readModuleData and the scanner's exact declaration comparison:70 constants,
zero type/definition/inductive/recursor/mutual metadata differences, zero proof-value
changes, same imports and extraConstNames. NGR_PIN_INPUT_HASHES verifies both
actual old/new bytes match the recorded hashes. Serialized files still differ;
no claim of byte-identical NGK object reuse is made. Environment extensions are
not compared by this shape check; the actual closure passes the full scan and
root audit. Sources/objects are read-only except this job's owned exports.

Receipts: NGR_ATTEMPTS.jsonl and per-attempt directories record exact target,
argv, source revision/hash, direct dependency/Aeneas hashes, exit, wall, peak RSS,
swap and full printed axiom lines. Every admission is exit0 AND allowed:true;
one6G/8G/swap0/tasks64 scope at a time; Lean -M7000; both links optimized-O3.
23/50 allocations (17 Lean,2 links,3 audits,1 raw comparison):19 success,
4 excluded elaboration drafts. Total wall108.368565s, peak7,007,656KiB, swap0.
No timeout, memory kill, cap raise or unchanged failed-shape retry. L002 had one
own-input missing export preflight, no compiler/scope; runner fixed, receipt kept.
Failures L003/L007/L008/L014 are excluded and their recovery sorryAx lines are
not imported by the final closure. No successful source has an admission hole.

This is a focused cached composition and audit, not a cold release replay.
No Kani, extraction, shipped-source edit or ELF rebuild was run. No ledger function
row is promoted: the NGP_HISTORY theorem implication is the delivered progress.
