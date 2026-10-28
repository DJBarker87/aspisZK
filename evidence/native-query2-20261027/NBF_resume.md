# Live continuation checklist

All work remains on codex/cx-native-query2-20261027; no pushes/merges.
Accepted Lean through L038. K019 circle scale routing is the next launched gate.
K001 type error, K006/K010 unwind errors, K014–K017 timeout: excluded.
L027 accidental unchanged replay: no credit; own runner guard now rejects it.
No cap/timeout changes. Current direct query composite is OPEN.

Remaining drafted Lean, in dependency order:
NBF_QueryLoop (imports checked QueryInitial), NBF_Node, NBF_QueryNode,
NBF_FinishTrace. Each needs focused compile and standard-axiom prints.
Then one final co-import audit of accepted public top theorems.

Final receipt work must archive every K source snapshot as a patch with
NBF_archive.py, collect all prefix/cache/library object hashes, validate frozen
crates/programs/lock, record exact budgets, remove only OWN Rust target and
solver temps. Keep persistent leaf cache forever. Retain all source and receipts;
no .olean/binary/ELF commit. Native scratch harnesses final deliverable should
be patches plus receipts. No shipped file changed, so no ELF rebuild trigger.

Independent native work can continue after a timeout: split one expression or
call cut; never unchanged shape, never multiplier equivalence in Kani, no
whole-buffer loops. Field stubs are paired in LPh_STUBS.md. All own authoring
scripts may be repaired but shared S2H/S2W infrastructure stays byte-identical.
