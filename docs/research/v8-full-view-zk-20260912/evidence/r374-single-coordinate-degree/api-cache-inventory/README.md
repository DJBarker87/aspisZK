# R374 polynomial API/cache inventory

Read-only inventory for the planned source-point polynomial degree work. `collect_inventory.py` walks the recursive Aspis import closure rooted at `AspisV8R19.SourceStatementPoints`, compares local source copies to the pinned host, and records host cache object presence and hashes. It did not invoke Lean or mutate/build a cache.

The closure contains 63 local Aspis/AspisFormal modules: every host source copy matches the local file and every corresponding pinned `.olean` exists. The 25 direct external imports observed across that closure have source and `.olean` files present under the recorded Mathlib package. As in the saved R370 cache inventory, this records object availability; it does not assert active `LEAN_PATH` resolution.

Exact polynomial API names, statements, source paths/checksums, and the distinction between the requested `Degree.Operations`/`Eval.Defs` modules and the actual `BigOperators` declarations are in `API_EXCERPTS.md` and `inventory.json`. This artifact selects no proof route and makes no theorem claim.
