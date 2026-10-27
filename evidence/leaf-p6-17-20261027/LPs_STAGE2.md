# Stage2: checked independent byte ports, not native closure

L101 LPs_CheckDomain.checked: actual compact.check_values success on SAME464
bytes derives all four natural LE word bounds for each of29 compact rows.
No canonicality premise, model whole-output equation or accepted field output
is input. Uses CLOSED LPl.Check.native_result and total trace.

L104 LPs_ExpandDomain.expanded: SAME29-row native trace yields length928,
low16-copy/high16-zero byte relation and actual compact.expand_values Result.
Reuses CLOSED LPn.Expand.native_result and inherited invariant; no buffer
normalization or native whole-buffer replay.

L105 LPs_NaturalDomain.selected: imports and applies LPr_SelectedWords to
LPq_ExpandedWords.canonical, deriving exact LPq ByteDomain from input length
and natural expanded/canonical predicates. No reproof of inherited ports.

All accepted roots print only standard axioms. L098 direct producer-consumer
join FAILS on duplicate root declaration; see LPs_IMPORT_FINDING.md. L100,
L102,L103 rejected snapshots and sorryAx lines are diagnostic, excluded.
No native closure or headline premise removal. No Kani/shipped/ELF change.
