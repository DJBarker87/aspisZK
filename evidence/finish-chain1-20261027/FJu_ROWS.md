# Assigned rows and exact remaining blockers

| Row | Original hypothesis location | Checked discharge | Remaining blocker for this row |
|---|---|---|---|
| F3Y_G_L144 | FJp_Top.finishOwners → FJp_Remaining.Holds → EquationEndpoint.initial | FJu_GlobalOwners.complete002, FJu_GlobalTop003, FJu_Top010; inherited FIr_PhysicalInitial.on_run on SAME e.run/parser/view/claim/polys | None in the installed dictionary |
| F3Y_G_L145 | Same global owner family → EquationEndpoint.chain | FJu_GlobalOwners.complete002; inherited FIr_PhysicalChain.on_run on SAME sourcePrepared/output/numeric and literal challenges | None in the installed dictionary |
| L144 | FJp_Result → ActualCaller → ActualCont → NativeLiteral → Finish.Outcome → ∀ semantic_S3_S9:EquationEndpoint.initial | FJu_NativeLiteral.strengthen006, FJu_Result.strengthen009, FJu_Top010 | None in the installed dictionary |
| L145 | Same native semantic hypothesis → EquationEndpoint.chain | FJu_NativeLiteral.strengthen006 with Fin9 quantifier intact; recursive chain induction inherited from FIr_Chain.adjacent via FIr_SourceChain | None in the installed dictionary |

FJu_NativeInitial.on_run012 and FJu_NativeChain.on_run013 are separately named
exact statement transports of the inherited physical laws; FJu_EndpointIdentity014
checks the retained endpoint is literally the same residual as FIr's. The full
native-local quantifiers and three parsing guards are retained. No callback is
used for initial/chain; the source-polynomial trace verifies them independently
of c.boundaries.terminal.

Remaining actual P rows by the inherited mechanical ledger: L142,
F3Y_G_L142 (Pair), L146,F3Y_G_L146 (semantic terminal), L154 (query budget).
Other workers own Pair/terminal; no credit for their work is included here.
All17 expanded deployment-only P obligations are retained. Frozen-source to
ELF association, the remaining extraction/runtime obligations, and joint
inhabitation of all deployed native/runtime premises remain open. No 100-bit
deployed release claim follows from these four implementation-law removals.

The FJp expanded mechanical baseline has89T/26P/13G; the human ledger prose
says89T/25P/13G. FJu_recount.py keeps the exact inherited row inventory and
method (17 deployment-only P rows) rather than silently dropping a row:
actual83T/9P/13G→83T/5P/13G; expanded89T/26P/13G→89T/22P/13G.
Delta0T/-4P/0G/0C. Native L143/global matching removals remain stacked.
