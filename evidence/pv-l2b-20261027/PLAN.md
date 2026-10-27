# L2 source trace task

Candidate: `c57a344726745387efb38d1571d885c69ce829ee`, branch
`codex/pv-l2b-20261027`. No implementation edits. Target not yet established.

Read common rulings (a)–(k), corrected (h'), restoration flag, AGENTS security
and proof discipline and D166. Compile budget 100; Kani budget 6 (control only).
IDs 53000–53299, final 53297–53299 reserved for audit; never reuse an ID.

Stages: capped rejection history and exact ideal sampler law; honest guard
invariants N2–N6; V371 and endpoint residuals; final axioms audit. Each stage
gets a path-limited commit. No N1 or N7 work. No keys created or cleaned up.

All sources and objects stay in the task host directory. Attempt 53000 showed
that the existing shared launcher rejects external sources under its fixed
`-R`. Subsequent attempts invoke its existing `run2.py` executor, unchanged,
with env/J.json and task-owned source/object roots inside prescribed scopes.
No shared source or object is changed. Standalone focused modules use only
standard mathematical imports; no ambiguous historical project module is
silently substituted. Every new theorem is audited with `#print axioms`.

Process deviation: 53038 retried the 53037 aggregate reservation refusal
after about 99 seconds rather than 180. Admission passed; memory caps and
reservation limits were respected, but the wait rule was violated. A local
timestamp check now refuses early retries. This is not hidden as a refusal.

Uniform independent candidates are an ideal law, not a claim about deterministic
SHA expansion. Native/ROM association and complete joint observation transport
must be named explicitly. A conditional guard lemma does not discharge the
deployed caller invariant.
