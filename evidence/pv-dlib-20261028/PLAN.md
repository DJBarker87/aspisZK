# PV_DL job record

Worktree `/Users/dominic/ZK/.worktrees/pv-dlib`; branch
`codex/pv-dlib-20261028`; base `b3ad0edf5b43d879f7b36abffdcb2d2fd30d0213`.
Read pv-common.txt (all appended rulings), pv-host-restored.flag,
r1p-common.txt, local-lean.txt, root AGENTS security discipline and LOG D42–D68.
Eight assigned rows, notwithstanding the phrase "recount 6": V187, V201,
V231, V234, V235, V236, V237, V238. No V232 work.

Limits: 100 Lean attempts; six Kani runs; IDs 42200–42299, audit reserve
42297–42299; one capped scope at a time. No source under crates/programs
changed. No shared source writes. No keys created or removed.

External preflight: every one of the 5,673 replay manifest paths matched,
and every selected object under the standing Env-J LEAN_PATH matched.
Authority: research:evidence/pv-replay-20261027/receipts/external-object-manifest.json.
The two verification receipts are read-only hash checks, not compiler runs.

Initial Charon admission 2026-10-28T00:38:33Z refused (exit 78): populated
reservation 59,995,324,416 bytes, safe limit 59,055,800,320 bytes. No compiler
started; no Lean attempt or Kani run charged. Retry after three minutes.

Process deviation retained: retry charon-default-02 was submitted about 130 s
after the first refusal rather than 180 s. It was admitted by both checks;
no reservation bypass occurred. Future refusals require the full wait.
The reference upload before the first admission is also recorded; no compiler
ran on that upload. Subsequent Lean uploads use admission receipts first.

42200: first focused Types compile failed before declaration checking because
Lean namespace lookup chose the partial commit54 directory and reported its
missing `Aeneas.olean`. The manifest-selected complete external module exists
and hashes correctly. Replacement environment adds a private external-object
link overlay before the partial project directories; no external object was
rebuilt or substituted. This is a changed environment, not an unchanged retry.

42201 was not launched: its second admission saw ENOENT for another session's
vanished cgroup (`session-326995.scope`). Under ruling (p'), wait at least 60 s
and retry the same unlaunched ID, at most three times. It is not a Lean charge.

42201 retry1 launched after the transient cgroup race; failed before theorem
checking: the new external link overlay lacked the IR companion for
Init.Prelude. Same-authority `.ir` companions are now linked read-only and
hashed separately. No library object was rebuilt. Both focused failures
are retained and charged. No theorem/row closure is inferred from extraction.

42202 upload admission refused 2026-10-28T00:43:54.652398Z (no compiler).
Next resource admission must be no earlier than 00:46:54.652398Z; use 42203
for the next focused Lean submission. Other scopes also wait for that point.

Native concrete SHA-256 constructor P6: kani-default-01 succeeds, 0/188
failed, three unreachable checks, no stubs/assumptions/compression evaluation.
Pinned isolated shipped wrapper attempt: Charon succeeds, but unchanged
pinned Aeneas rejects its LLBC at the fail-closed escaping-reference/structured
Drop preflight. The rejected candidate is retained; it is not a false-row
counterexample or a stop. Continue P6 with an owned generic moved-core reference.

42206–42209 passed (generic owned reference plus private h5 type dependencies).
42210 pre-upload admission refused at 00:55:36.450630Z: aggregate reservations;
no compiler started. Next resource admission no earlier than 00:58:36.450630Z.

42211–42215 passed. 42216 second admission refused at
00:59:33.062645Z (aggregate reservation). No compiler started for that ID.
Next resource admission no earlier than 01:02:33.062645Z, with fresh ID 42217.

The update reference relates active buffer prefixes, not dead suffix bytes:
block-buffer's batched path may leave different bytes outside `get_data()`.
A raw full-buffer equality would be too strong. The planned padding event gate
must show that these dead suffix bytes are overwritten before compression.
No raw-state/native equivalence is claimed from active-prefix equality alone.
