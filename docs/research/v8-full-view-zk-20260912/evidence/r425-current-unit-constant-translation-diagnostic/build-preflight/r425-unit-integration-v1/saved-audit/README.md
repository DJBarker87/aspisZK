# R425 integration saved-run audit

Read-only audit of the saved `aeneas__InterpExpressions.cmo` compile. Run `python3 audit_saved_run.py` from any directory; it reads only adjacent saved run artifacts and candidate input snapshots, and writes its derived audit and metrics records beside itself. It does not invoke a compiler or mutate archived source/log receipts.

`audit.json` records the per-artifact checks. `metrics-receipt.json` records the compiler GNU-time measurements and Docker/systemd resource scope. `SHA256SUMS` covers the checker, report, audit, and metrics receipt. Axiom reporting is not applicable to this OCaml compilation.
