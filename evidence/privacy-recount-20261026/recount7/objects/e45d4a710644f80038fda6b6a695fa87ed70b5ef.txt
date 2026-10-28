# pv-reach8 final report — LOG D327

**Target not yet established. V404 OPEN → OPEN; V405 OPEN → OPEN.**
No endpoint premise, deployment condition or T field was removed, added or
weakened. Step 1 is incomplete; InstalledOp84 was not compiled. Step 2's
exclusions, native success/non-vacuity witnesses and minimal reached sets remain
unproved. This run adds evidence and checking scripts, not Lean theorems.

Exact worktree `/Users/dominic/ZK/.worktrees/pv-reach`, branch
`codex/pv-reach-20261027`, start `ff32e6963640608feef157f8cdd445d12e74daab`.
Stage commit: `22e65beb67`; this report is committed separately. No push.

The 200 actual prerequisites are listed in `prerequisites-before.txt`.
The requested runjoin20 certificate covers 669 objects but **none of these
200**. A wider read-only Stream B cache search found candidate paths for every
prerequisite. None was verified against all three h6 requirements. The copied
join cache records 147 matching sources without original build provenance or a
complete historical fingerprint. Matching-source successful Stream B receipts
were found for 67 modules. Runjoin symlinks into Stream A were not imported.

Current complete dependency comparisons found mismatches for 188 modules and
unavailable private transitive objects for 179 (overlapping categories).
Candidate compile environments were not certified identical. For example,
cb's recorded Op84Exact build requires a different Op84Funs object hash from
this job's selected object. Exact checks and limitations are in
`h6-prerequisite-dispositions.json`, `environment-fingerprints.json` and
`FEASIBILITY.md`. Source equality alone was not promoted to verified reuse;
EJR/freeze precedence was retained.

With presently verified evidence, step 1 needs **200 prerequisite builds plus
InstalledOp84 = at least 201 attempts**, or 204 including three audits. Even
optimistically qualifying all 67 matching-source build records leaves **134
attempts before audits or step 2**. Step 2's initial estimate adds at least 12
modules/22 substantive statements, plus missing guard/native-effect transport.
It cannot plausibly finish within 100 attempts. Under the ninth-round lead
note and AGENTS.md section 7, this run stops at the feasibility finding without
spending the budget on a partial prerequisite prefix or more wrappers.

Validation: all 5,673 effective h4 external hashes match; evidence consistency
and Python syntax checks pass. **0 Lean, 0 Kani, 0 scopes, 0 IDs consumed.**
39900–39999, including audit IDs 39997–39999, remain unused. No new theorem
requires an axioms audit; compile target/exit/RSS/swap/axioms receipts are N/A.
The prior unlaunched 39406/39476 handling errors remain explicitly recorded as
zero compiles and were not reused. No new handling error occurred.

No Lean/shipped source, host file, compiled object, key, shared environment,
launcher or sibling worktree changed. Native associations and non-vacuity
remain exactly as in resume7/native-boundary-review.md. Row comparison is
preserved in `row-comparison.json`. No counterexample, failed lemma, host fault
or reservation refusal is claimed. Next: `next-deliverable.md`.
