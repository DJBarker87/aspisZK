# Hir history3 stage 0

Target not yet established. No ledger rows removed.

The actual T2R_Top.deployed endpoint exports history and P2Prime inside
T2R_Acceptance.Facts and T2R_CallerSource.Outcome continuations. Recount must
expand those continuations, not only count visible theorem binders.

First work: exact partial-source transcript transport, then adaptive scheduler
with computed store/entry association and all Q1 reads in one oracle program.
Second work: extract and check complete Pool checkpoint lifecycle from unchanged
source, splitting the borrowed zero/fresh guard which previously failed Aeneas.
Only after both concrete instances are checked can the six target rows be
removed from a strengthened Hir_Top.deployed. L159 belongs to another job.

Use one host scope at a time, 6G/8G/0/64, Lean -j1 -M7000. Reuse coherent
SInt2/Hist/Hiq/RawJ objects. No package replay. No source/SDK assumptions may
be added in place of a missing concrete instance. Existing SDK and Solana
runtime trust stays explicit. No shipped source or key changes planned.
