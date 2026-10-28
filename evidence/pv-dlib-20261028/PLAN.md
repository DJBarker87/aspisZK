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

42218–42220 passed. 42221 failed on record-field layout in the new selected
dictionary (unexpected identifier); its failed elaboration reports sorryAx.
That failed object is not imported or credited. Fix the layout and compile
the changed source with the next fresh ID before dependent targets.

42222 selected default compiled with standard axioms. 42223 callback statement
failed because its explicit `@ExternalFuns.op217` application omitted the five
implicit Type arguments. Correct those arguments; no theorem statement is
credited from the failed attempt. 42224 is the next fresh focused ID.

42224 correctly exposed a carrier mismatch in the draft statement:
BufferKindUser captured `base` rather than `Types base`. Make that instance
argument explicit in the callback and native constructor statements. This is
a typed-carrier correction, not a source-law premise or a weakened success guard.

42225 was a resource refusal at 01:11:07.873518Z; next eligible admission
01:14:07.873518Z. 42226 launched after that time and caught an implicit
projection instance in the draft size guard. Replace dot projection on
BufferKindUser with an explicitly carrier-indexed projection helper.

42227 upload admission refused 01:17:47.572720Z (aggregate reservation),
no compiler. Next resource admission no earlier than 01:20:47.572720Z.
Private wrapper now refuses an already charged source/import/environment
input. The earlier Types loader repairs had three distinct environments:
partial Env-J namespace; pinned external overlay without IR companions;
pinned external overlay with same-authority hashed IR companions. No failed
source was intentionally re-run against unchanged actual inputs.

42242 compression-parameter trace transport passed. 42243 failed because the
new theorem name `partial` is reserved Lean syntax; rename it `pending`.
The update reference is strengthened to retain callback batch boundaries and
all 64 buffer bytes. The earlier byte-at-a-time reference remains as a
blockwise model candidate, not a general arbitrary-batch callback law.

Kani update-03 ten-minute resource review: the active optimized harness is
control/indexing/batch grouping only; no SHA compression or field chain is
reachable from its target. Keep the unchanged 6G/8G/no-swap caps and existing
900-second timeout; do not extend it. A distinct follow-up candidate uses
symbolic event/byte coordinates and unwind 70 (same input bounds), avoiding
whole-array comparison formulas. It is not launched in parallel.

Kani update-03 exited 124 at 900 seconds (wall 15:01.20). Optimized compilation
finished in 0.96 s; time was spent in verification, not an unoptimized build.
No counterexample or proof was returned. The actual source unwind was 132;
the generic receipt label inherited 196 and has been corrected explicitly.
The post-timeout scope check found the recorded own cgroup removed and no
remaining processes. GNU-time RSS is retained; aggregate peak was unavailable
after scope removal. Next candidate: same input bounds, symbolic coordinates,
unwind 70, same caps. No unchanged retry and no cap/timeout increase.
