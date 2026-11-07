# Returned-observation gate continuation

Binding ruling: C3-BIN (bq) clarification, 2026-11-07, now merged. ReturnFunctional quantifies over two returned observations at the same Env and proves equality of the entire Obs, including events. Abort/diverge/prefix arms remain unrestricted. No RSL module or previously proved LIBB module is changed.

L325 defines LIBB_ReturnFunctional.ReturnFunctional. L328 compiles the generic log Safe invariant lemmas. L335 proves LIBB_ReturnRun.run by source-constructor traversal without unfolding child calls. L336 proves LIBB_ReturnObservation.functional for the full Slice law: a returned parent has no failed Merkle child, so every Piece has the unique complete expansion; independent outer stopped arms cannot return. Every top theorem prints standard-only axioms. Byte transport/gate and module13 admission are the next targets.

Original source/native fold, original Dom064, Env.reservation reading, and unchanged NNC_ObservedLaw.w registration are reused byte-identically from the prior continuation. I.f064 and SAME-runtime EnvRep binding remain integration-owned. No ledger credit or final security result is claimed. This is the same200-scope authorization, resuming at L325 with176 remaining. No Kani/extraction.
