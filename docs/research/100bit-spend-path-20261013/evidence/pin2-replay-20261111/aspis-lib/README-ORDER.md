# Trimmed-copy pipeline (order matters)
1. trim_imports.py <l187src> <out> <closure-kind-d.tsv> --map (IMPORT_MAP.txt rows) <modules...>: carrier imports -> base module imports; unmapped carriers and OMIT_MODULES removed from import lines (add OMIT_MODULES.txt rows to the d-list file, or pass them as unmapped carriers).
2. drop_decls.py <l187src> <out> DROP_DECLS.tsv: deletes the 16 named declarations from the 10 modules (reads the trimmed copy if present). DROP_RECORD.tsv: module, decl, line span in the file as edited (after the import trim), sha256 of the removed text.
3. Compile in import order: AspisLib_SourceInputs, AspisLib_Recorded, AspisLib_QueryAccounting first; then every trimmed module; AspisLib_Tag and AspisLib_Guard where their imports are ready; chain modules last. Trimmed objects shadow the L187 objects on LEAN_PATH; a module importing a carrier and a base together fails by name clash, which is the intended check.
4. Modules in OMIT_MODULES.txt (16, no needed constant) are not compiled; any needed module importing one gets that import line removed in step 1 (treat them as unmapped carriers).

## Revision 4 (2026-11-12)
- trim_imports.py: `--omit OMIT_MODULES.txt`; an import of an unmapped carrier or an omitted module is replaced by that module's carrier-free import frontier (recursively; mapped carriers become their bases), never deleted. Duplicate import lines are collapsed.
- drop_decls.py: command lines (`#print axioms`, `#check`, ...) naming a dropped declaration are removed with it and recorded.
- Bases regenerated with omitted modules expanded: AspisLib_Tag and AspisLib_Guard import no carrier and no omitted module directly.
- Gate: X3's graph check (no carrier or omitted module in the import closure of anything compiled), not the compile exit; Lean 4.32 loads a shadowed L187 object silently.

## Revision 5 (2026-11-12): omit list tightened
Rule for the omit/drop lists: a module goes on OMIT only when most of its declarations use carrier content; a module with a few carrier-using declarations is KEPT and those declarations are DROPPED (its namespace stays available to `open` lines downstream). Moved from OMIT to KEEP+DROP: R15WriterModel (acceptance_alone_obstruction), R16DecisionErasure (accepted_without_instance), R19BudgetOriginalReads (original_reads), R9PoolSavedTenModel (prepare_original, resume_recorded). OMIT now 12. Cascade rule (zk-73/X3) confirmed: an un-needed module failing on an omitted module, dropped declaration or carrier is omitted; an un-needed declaration inside a needed module failing the same way is dropped; a NEEDED declaration failing stops the run; every addition recorded with error and dependency. Tie-breaker: a failure at an `open X` line means X must be kept and trimmed, not omitted.
