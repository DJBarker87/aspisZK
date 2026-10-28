# pv-runjoin14 resumed under D275

**Target not yet established. Stage 3 remains open.** Branch
`codex/pv-runjoin-20261026`, entry `503344e60f`.
Final shipped source revision `c58e0473ac60090f016a59e3b7953f429de2d5c2`.

## Repairs

The existing closure rewrite `2910da23a3` and pair-copy repair `05cb63a2ea`
are retained. This resume commits exactly two further changes inside `records`:

- `4fd383fc99`: range `for level in 0..24` becomes indexed `while level < 24`,
  incremented after the identical body (authorized kind iii).
- `c58e0473ac`: entry `let input = *input;`, replacing shared input uses with
  an immutable copy (kind i; Copy derive `pair_forest_trace.rs:53`).

Verbatim repairs and justifications are in `REPAIRS.md`. The resume source diff
is `shipped-records-d275.diff`; `source-freeze-audit-d275.json` verifies unchanged
signature and all file bytes outside records, with no other shipped path changed.
All 510 tracked crates/programs/lockfile files byte-match the private host
snapshot (`host-source-agreement-d275.json`). No shared env-J source write,
merge, push, repin, wallet-key deletion, observer/simulator change or T addition.

## Gate (a)

**PASSED** after the final source repair; all three pins MATCH (`gate-a-d275.json`).

| Target | Exit | Wall s | Peak RSS KiB | Swap | ELF bytes |
|---|---:|---:|---:|---:|---:|
| default | 0 | 68.398 | 682936 | 0 | 1563728 |
| devnet | 0 | 70.78 | 683120 | 0 | 1563728 |
| pool | 0 | 67.363 | 675012 | 0 | 605704 |

SHA-256 (expected = actual):

- default: `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet: `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool: `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

The existing private gate13 workspace and pinned SBF command/environment/cache
were reused; three fresh output directories preserve the build cohort.
New artifact keys remain on the host at mode 0600 (`key-retention-d275.json`),
with no key contents, ELF or compiled objects copied into evidence.

## Extraction and stop

Both diagnostic Charon runs (02/03) exit 0 with clean preflight and records
body retained (`extraction-preflight-d275.json`). Pinned tool hashes match the
previous stage. Both corresponding Aeneas runs exit 2. The range intrinsic is
cleared, but the sibling tuple branch join fails in `InterpBorrows.ml:2731`:
latest source span `records:238:15–242:9`. See `BLOCKER-D275.md` for exact
stack location and retained LLBC shared-index-borrow nodes. The second witness
copy is present in LLBC but does not clear this next boundary.

The smallest next source candidate is a branch-body restructuring that moves
bit/sibling stores into each branch. Its exact **unapplied, untested** proposal
is `UNAPPLIED-branch-proposal-d275.diff`. It is not one of (i)–(iii), so this
route stops under the user's explicit boundary. No extractor patch or assumed
source equality is introduced. This is a failure of this pinned configuration,
not a proof of impossibility for every extraction configuration.
Raw's earlier outside-records FnOnce obstruction remains historical evidence;
raw and empty-root concrete links are still required by this isolation.
No R_shipped definition has been emitted/accepted, and no unchanged failed
extraction is repeated. These diagnostic extractions locate the last repair
before final ELF gating; none is accepted as a release extraction/theorem.


Extraction resource summary (source revisions are recorded per exact command):

| Target | Source revision | Exit | Wall s | Peak RSS bytes | Swap |
|---|---|---:|---:|---:|---:|
| pv14-records-charon-02 | 4fd383fc99 | 0 | 49.208320 | 1330352128 | 0 |
| pv14-records-aeneas-02 | 4fd383fc99 | 2 | 0.604006 | 85372928 | 0 |
| pv14-records-charon-03 | c58e0473ac | 0 | 46.039304 | 1291726848 | 0 |
| pv14-records-aeneas-03 | c58e0473ac | 2 | 0.812845 | 86974464 | 0 |

## Proof and trust status

Transfer identification: **OPEN**. Withdrawal identification: **OPEN**.
General identification: **OPEN**. Compiler-return equation, transition equality
at each fixture's actual selected i, deployed public binding, and P ∧ T
non-vacuity: **OPEN**. The 21 previously proved mathematical empty-root cells
and research PV_Src_* results are retained, not relabelled as shipped facts.

Constructed P before/after: {source public binding, trace} → same.
Deployed P before/after: OPEN → OPEN. Record counts: 2/8/6 → 2/8/6.
Endpoint premises removed/added/weakened: 0/0/0. No quantifier, carrier,
failure event or conclusion is changed. T stays exactly entropy_law,
entropy_kernel, observation, and is hypothetical. `P-before-after-d275.json`
and `trust-audit-status-d275.md` contain the explicit trust review.

No new Lean theorem, kernel audit or standard-axiom result is claimed;
#print axioms is N/A for these tool runs. All seven host runs have exact
commands, exit, wall, peak RSS, swap, controls and source revision recorded in
`receipt-index-d275.json` and the referenced raw receipts. All scopes used
6G/8G/swap 0/TasksMax 64, one at a time, with admitted reservation receipts.
Expected work: optimized source/MIR compilation, Aeneas translation, or optimized
SBF compilation; no dense elimination or arithmetic Kani run.

Budget: **0/100 Lean, 0/2 Kani**; 50600–50899 remain unused, including final
50897–50899 reserved for a focused audit. This stop is an explicit repair-scope
boundary, not exhaustion or a checked ROW counterexample. Gates (b)/(c) remain
lead-owned under runjoin13/GATE-PLAN.md.

Next deliverable: lead ruling on the branch-body proposal, or a specified
pinned-extractor route that avoids that join within the existing repair scope;
then source extraction with concrete helper links, transfer/withdrawal/general
identification, compiler return, selected-i transition, public binding and
non-vacuity, followed by a focused kernel trust audit. No privacy target claim.
