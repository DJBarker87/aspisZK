# pv-runjoin11 — exact source-leaf obstruction

**Target not yet established. Requested selected-record deliverable remains incomplete.**
Branch `codex/pv-runjoin-20261026`; entry `623a1d3be6`. No push.

Both fixtures still have **no actual selected-record Lean term**, no compiler-return
equation, no deployed source public binding, and no P ∧ T non-vacuity proof.
`PV_RunJoin_RecordedTransfer` and `PV_RunJoin_RecordedWithdrawal` provide only
literal publicRecord/transition/publicInput data from the pinned 1880-byte terminal
fixtures at ed1c1cef71. The generator passed --check. This is byte-field extraction
plus carrier typechecking, not a theorem about the Rust decoder or compiler return.
There is no arbitrary compiled parameter presented as actual deployed data.

The exact missing mapper proposition for each fixture and its shipped locations
are recorded in stage1-missing-fact.md and stage2-missing-fact.md. The shipped
records leaf remains a class parameter in the port; the owned dynamic dictionary
has not been identified with that leaf. Stop each stage there under the explicit
missing-fact instruction; no new conditional bridges were proved around it.
Runtime/observer installation and stage 4 were not started. The source facts are
not ROW counterexamples. No full manifest or coherent release replay is claimed.

Constructed P **{source public binding, trace} → {source public binding, trace}**;
deployed P unchanged and OPEN. Endpoint rows removed/added/weakened: **0/0/0**.
Record counts **2/8/6 → 2/8/6**. T unchanged: entropy_law, entropy_kernel,
observation; T hypothetical; A/B unadopted. Exact prior before/after statements
are retained in P-before-after.json with fixture status. Original endpoint sources
are unchanged (final-source-audit.json).

Source root cells 18 and 19 passed with the unchanged optimized Kani configuration,
no stubs; combined historical coverage **19/21 → 21/21**. These checks do not
prove a mapper equality, compiler success, source public binding, or L2 trace.
The original 25 missing objects remain restored; the remaining 11 L2 objects
were not attempted.

Validation: **5/100 Lean attempts**, 5 accepted;
**2/4 Kani runs**, 2 successful. IDs
40300–40304 used once, next 40305;
no reservation refusals. Last three actual Lean attempts are the focused trust
audit. All axiom reports are subsets of [propext, Classical.choice, Quot.sound].
Every receipt includes exact target, exit, wall, peak RSS, swap, revision, source
snapshot/hash, dependency fingerprint, full axiom output and caps. Kani axioms N/A.
Shared launcher TasksMax=128 under lead ruling (b); own Kani scopes TasksMax=64.
All runs had swap zero. Raw receipts/logs and receipt-index.tsv are retained.

| ID | Target | Exit | Wall s | Peak RSS bytes | Swap |
|---:|---|---:|---:|---:|---:|
| 40300 | R1Z/PV_RunJoin_RecordedTransfer | 0 | 2.34 | 4209889280 | 0 |
| 40301 | R1Z/PV_RunJoin_RecordedWithdrawal | 0 | 2.34 | 4211818496 | 0 |
| 40302 | R1Z/PV_RunJoin_TrustAudit11Recorded | 0 | 1.67 | 4177768448 | 0 |
| 40303 | R1Z/PV_RunJoin_TrustAudit11Compiler | 0 | 1.76 | 4176896000 | 0 |
| 40304 | R1Z/PV_RunJoin_TrustAudit11Endpoint | 0 | 1.75 | 4464295936 | 0 |

**Allocation is not exhausted:** 95 Lean attempts and 2 Kani
runs remain. This is an explicit missing-fact stage stop, not an exhaustion claim
or a claim to have fulfilled the whole-budget instruction. Dependent stages
remain gated; spending the rest on more bridges would violate the requested
focus. The target and requested main deliverable remain unestablished.

Next deliverable: identify the shipped Records leaf at the same transfer fixture
arguments, then construct the actual selected Input and prove its compiler-return
and equality to RecordedTransfer.transition; repeat for withdrawal before installing
runtime/observer and proving P ∧ T non-vacuity.

Only the pre-existing cfg(kani) child gained the two harnesses; no production body,
ELF pin, simulator, observer, wallet or key changed. Final build cache cleanup is
recorded separately. Commits are in COMMITS.txt.
