# Coordinator checkpoint — 24 October 2026, 11:05 UK

Active user-requested goal: establish both deployed security targets under the
binding contract, by continuing worker review, integration and relaunch until
closure or a genuine decision requiring the owner. Both targets are currently
not yet established. Root branch research; session A files remain untouched.

Q1 and Q2 were reviewed, merged and pushed through 6394df2389. Both old
worktrees and local branches were removed after verifying merge ancestry,
clean status and absence of ignored files. Neither branch existed on origin.
No keys or shipped files were involved. C3-BIN records the exact accepted
conditional claims and validation; LOG D190 records the entropy obstruction.

| Active worker | Worktree / branch | Deliverable | Hard budget |
|---|---|---|---|
| Entropy effects | .worktrees/cx-prover-rw / codex/cx-prover-rw-20261023 | Actual entropy/retry interpretation with changing state and preserved E1/L1/L2; retain counterexample | Remaining 40 Lean, 18 Kani; J 11262–11399, check unused IDs |
| Checkpoint integration | .worktrees/cx-port6ck / codex/cx-port6ck-20261024 | Native op18 helper composition and same saved-to-resumed state for Q1/Q2 | 100 Lean, 40 Kani |
| Authentication and security transport | .worktrees/cx-port6auth / codex/cx-port6auth-20261024 | Indexed recovery from actual batch/log; resolve clean-event versus all-oracle join mismatch without weakening the contract | 100 Lean, 20 Kani |

All use gpt-6.1-sol, medium, codex-run.sh. Output names in the inherited
scratchpad: codex-prover-effects-20261024.out, codex-port6ck-20261024.out,
codex-port6auth-20261024.out. A terminal codex-exit marker triggers review.
Prompts are preserved under evidence/coordinator-20261024 with hashes.
Check terminal markers without reading long live outputs. Capacity errors:
retain WIP, wait about a minute, resume with the same remaining budget.

Critical interface finding: Q1 indexed authentication uses existing Merkle
recovery outside the charged collision event; AcceptedVerifierJoin currently
quantifies over every H. No all-oracle join is credited from clean-event
recovery. The authentication worker must either derive sufficient unconditional
source consistency or prove good-event experiment transport with the exact
existing collision allowance and annotation/query accounting. No counterexample
to the strong join has yet been established by the lead.

Parallel Lean window ends at 14:00 Europe/London; verify each worker's launcher
switches to the shared global lock outside 22:30–14:00. Caps remain independent
6G/8G/no-swap, or the inherited stricter privacy 5G/7G. Aggregate reservations
must remain below 55 GiB. Do not increase caps. No repeated final manifest.

Next review checks: exact statements and hidden premises; source/receipt hashes
and standard axioms; no crates/programs delta without all-three current ELF
gates; no source adoption without equivalence/performance gates; same execution
and ordered oracle effects; retain failed evidence. Merge only reviewed scope,
append ruling/status, push research, then remove only fully merged clean owned
worktrees. Prover and CT candidates remain unmerged until all adoption gates.


## Prover adoption source audit — 24 October 2026

Read-only comparison at candidate 7db89a0216 found that research's approved
H5 commit 60cb14bde2 is missing from the candidate. Its four source deltas are
state_only_prefix.rs, fast_pairing.rs, weights.rs and r1_pool_adapter_owned.rs.
The candidate's recorded complete ELF identities are d7d42f77…/2b2a9f0e…/
121f3e29…, not current f8c0ec72…/63ad3e9c…/121f3e29…. Historical identity
is therefore insufficient for adoption, as anticipated by the handoff.

After the active entropy job commits and releases its worktree, integrate the
already-approved H5 source revision into the candidate (no new protocol or
verifier change is authorized). Assess exact affected proof/extraction
closures, regenerate only affected targets, and rebuild all three ELFs against
the current pins. Entropy source is outside H5's four-file delta, but full
caller emission/external dictionary numbering may change: bind operations by
qualified source name and exact body/signature hashes, never by an inherited
op number alone. The old fixed-tape obstruction remains pinned evidence.

Then run the candidate's fixed-coin differential and performance gates only
where source/artifact changes invalidate old evidence. The under-15-second
absolute gate must use a quiet build host; any >10% fixture slowdown is a stop
for review. The ongoing entropy proof is not interrupted merely to rebase its
source snapshot. Candidate adoption remains blocked on these concrete gates,
real-prover refinement and the remaining side-channel obligations.


## Quiet-host prerequisite (2026-10-24 11:16 UK)

Session A solver PID 2095724 is still CPU-active after more than 32 hours,
PPID 1, ~4.7 GiB RSS in its 8 GiB no-swap scope. Exact owner/workspace and
scope are recorded in HANDOFF-SESSION-A. The lead did not stop it. Obtain an
owner resolution before calling the host quiet; ordinary capped focused proofs
can continue within the 55 GiB aggregate reservation ceiling.
