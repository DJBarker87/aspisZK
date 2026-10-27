# Final receipt notes

The retained raw launch capture contains one whitespace-only line at Rc12_001-launch.log:15, produced by the upstream pretty-printer. The raw bytes are preserved. Authored-source/prose whitespace validation excludes only that raw file; all other paths pass. This is not a Lean diagnostic or proof failure.

Rc12_recount.py initially rejected the ARX statement comparison because #check prints a leading @ while #print prints theorem. The mechanical checker now removes exactly the initial @ before substring comparison; the complete remainder of the type must still match. No Lean source or proof was changed and no compiler retry occurred. Rc12_statement-check.json records the successful full-type comparison.

Stage 1 commit: 42a5460bc8. Stage 2 includes the focused compile receipts, mechanical row inventory and delta, one-page status, validation and terminal-scope cleanup. Only the owned query object was removed; shared caches and all keys retained. The nine unused Lean attempts are not exhausted: this resume authorized a mechanical recount, which is complete.
