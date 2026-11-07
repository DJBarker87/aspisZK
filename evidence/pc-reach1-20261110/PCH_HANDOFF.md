# PCH reachability handoff

Stage 1 authority audit in progress. No exclusions or ledger changes admitted.
Branch codex/pc-reach1-20261110. Scope: 278 new NKZ ON Pool occurrences only.
No Kani or Lean proofs are authorized or run. Frozen files and sibling worktrees remain unchanged.
The retained Pool ELF receipt matches e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc,
but NKZ_aspis_pool.command.json names the 1.89.0-sbpf-solana-v1.52 compiler,
whereas ruling (c-g)(2)(a) requires rustc 1.94.1. This must be resolved before graph authority.
Stages 2–4 depend on Stage 1 admission; no conservative graph is promoted.
Target not yet established.

Stage 1 completed as a blocked authority audit (PCH_AUTHORITY.json).
The retained receipt establishes the expected ELF hash for rustc 1.89.0-dev,
NOT rustc 1.94.1. Host PCH_A001 independently checked the pinned compiler hash
and version and both compilers' supported target lists. Native rustc 1.94.1
has no sbpf-solana-solana target. Receipt native_rustc_version is not the SBF
compiler version. All retained compiler-source checks match the requested
frozen revisions; the frozen lock and receipt before/after hashes match.

No rebuild was launched: the specified 1.94.1/SBF toolchain is unavailable,
and repeating the retained 1.89 build cannot meet the literal authority rule.
Per the explicit Stage 1 stop instruction, no graph/exclusion is admitted.
One admitted capped script/audit scope used; zero build/Kani/Lean scopes.
PCH_A001 exit 0, wall 0.12 s, peak RSS 45760 KiB, swaps 0; axioms N/A.
Host free space 163604512768 bytes before scope; reservation allowed true,
exit 0. Only own cache created; no cache corpus copied because blocked
before graph construction. No Aeneas object selection or LEAN_PATH used.

Final disposition: explicit Stage 1 stop, not completed stages 2–4.
PCH_FINDINGS.md contains PCH-F1 and the concrete lead remedy. PCH_REMAINING.md
lists all 278 members and explains the unused budget for each. PCH_VERDICTS.json
records NOT ASSESSED (null verdict), never an unresolved-edge or exclusion claim.
Graph and validator implementation are intentionally absent; PCH_VALIDATION.json
records all five mutation tests NOT RUN. The empty PCH_LEDGER_DELTA.json changes
no row, including live PCD_/PCF_ rows. PCH_COUNT.md preserves 39 inherited CLOSED,
0 exclusions, 239 OPEN (A74/B124/C11/D30); reachable counts remain unknown.
No assumptions discharged, retained trust unchanged, none added or reclassified.
No new theorem and #print axioms N/A. No transaction shapes or exploit inputs.
No shipped files, siblings, host infrastructure or keys modified; no push.
