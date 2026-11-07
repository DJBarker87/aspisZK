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
