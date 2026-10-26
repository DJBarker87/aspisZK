# Runtime5 event-transport handoff

**Target not yet established. No premise removed from Rc7_Top.deployed.**
Branch codex/cx-l159-runtime5-20261026; stage commits local, no push/merge.

## Exact stopping obligation

The full kernel-checked formula is
`AspisR1.SCF_RequiredTransport.CleanAccountTransport` in
lean/SCF_RequiredTransport.lean and SCF_014/stdout.log. Substitute the
Rc7-installed configuration and retained installation/native/runtime/game
laws; the required conclusion, for EVERY oracle H on the SAME adversary a, is:

    accepted(account a H) AND NOT chargedCollision(account a H,Q0+Q1+2965)
      -> accepted(projectedFrozen3(submission a) H)
         AND RecoveredInputAgreement(physicalAccountView, projectedFrozen3View)

This is a named UNPROVED TARGET, not an adopted trust item, not a proved
transport, and not an additional retained premise of a new deployed theorem.
No SCF_Top.deployed has been fabricated by assuming it. The next application
of the generic event consumer would need precisely this extra hypothesis;
work stops before installing it, under the instruction to stop rather than
add a premise outside the retained list. Independence from the retained laws
is NOT proved; the local deletion countermodel is NOT such an independence
proof or a counterexample to the physical account instance.

More concretely, the causal recovery route still needs the actual sampler's
reads in the ORIGINAL first-wrapper prefix, on the SAME submitted public and
proof. The required read-containment statement is:

    forall addr,
      Read (eval H (RawCutProverCompiler.verifier D false pub pf)).log addr ->
      Read ((eval H a.first).log ++
            (eval H (SCE_Execution.firstCode ... (eval H a.first).output)).log) addr

Here `false` abbreviates the two-argument constantly false decision; pub/pf
must be derived from those submitted bytes, with valid constructor schedule.
Also missing is accepted second-input/source association or its charged
collision alternative on this SAME physical account recorder. FGl_Join
charges a different source-account program. Equal bounds on the two recorder
programs do not prove event association. No new cryptographic/trust premise,
metric, query term or reduced security target is proposed.

## Proved and not proved

- SCF_Charge.charged: ORIGINAL fully adaptive account source occurrences
  <=Q0+Q1+1921, recorder first reads<=Q0+Q1+2965 and collision mass bounded by
  the SAME accountLoss(Q0+Q1). Includes rejected prefixes and all outer queries.
- SCF_Cuts/Deletion/Recovery: exact recovered words/input interface and
  per-coin extractor equality from replayed frame/first-cut agreement;
  deletion after a common first-read prefix preserves the cuts.
- SCF_FrameReplay.recorded: fresh outer addresses are safe for replay if the
  actual sampler reads are retained; no global known-suffix requirement.
- SCF_AccountCuts.delete_choice: on the original response-driven account,
  deleting second-choice queries preserves cuts already reached in TX1,
  including when TX2 rejects. The deleted log is pointwise, not a new
  generative/free-query adversary or an identified headline source program.
- SCF_Domination.pointwise_of_agreement: generic conditional event consumer;
  failureMass(left)<=failureMass(right)+indicator(charged collision).
  The actual physical account instance remains UNPROVED.
- SCF_Obstruction: consistency and ordered-subsequence containment alone do
  not imply local executable recovery preservation. Only a tiny binary
  leaf primitive is used; no accepted full protocol/forgery claim.

No concrete extractor implementation/traversal cost refinement is newly
proved. The occurrence and first-read bounds are formal; they must not be
promoted into a full implementation bit-cost theorem.

## Actual top, before/after and recount

SCF_BEFORE.lean.txt and SCF_AFTER.lean.txt are byte-identical Rc7 source;
SCF_BEFORE_KERNEL.lean.txt and SCF_AFTER_KERNEL.lean.txt are its identical
fresh kernel statement. No quantifier, carrier, event, conclusion or retained
hypothesis is changed. The source and host root hashes agree exactly.
The ledger method re-enumerates every inherited atomic family, preserving
all quantified guards/witnesses and eleven game clauses. SCF_LEDGER_DELTA.json:

- Actual83T/26P/13G/0C -> unchanged.
- Deduplicated deployment-inclusive89T/31P/13G/0C -> unchanged.
- All audit rows89T/32P/13G/0C -> unchanged.
- Removed0, added0, reclassified0. L159/L185 and L181 remain OPEN.

The expanded RPx/Rc7 family catalogs are inherited and hashed, not freshly
replayed. No structure-wrapper discount or conditional consumer is counted
as discharge. The shared-adversary account domain is the existing SCE domain;
no new theorem restricts the old unrestricted Rc7 runtime quantifiers.

## Non-vacuity and validation scope

SCF_Nonvacuity.joint simultaneously retains SCE's native successes, real JFx
public/stored bytes, admissions, SDK/std, game, persistence, checkpoint and
nonempty history, and adds the original account1921 occurrence and zero-query
collision-charge bounds. Its source acceptance remains computed. It proves
neither CleanAccountTransport nor joint instantiation of every retained
cryptographic/extraction boundary. No full release-premise inhabitation claim.

SCF_VALIDATION.json gives final measured totals and passing exact-source map.
Every current new module has a passing focused host receipt. New top theorems
are audited with #print axioms; only propext/Classical.choice/Quot.sound or
subsets occur in passing results. Failed elaborations, including their
error-recovery sorryAx lines, are retained and excluded. No sorry/admit/axiom/
native_decide or heartbeat/depth override is in a current new source.

One scope at a time, unchanged S2W launchers,6G high/8G max/Swap0/Tasks64,
Lean-j1-M7000-async=false, coherent SInt2 objects reused. No dependency build,
Rust, Kani, memory kill, timeout, cap increase or package replay. SCF_004 was
rejected by dependency preflight before Lean; the other exclusions are local
elaboration failures described in stage notes. Source_revision fields are
prepared-source git anchors with exact dirty snapshots/hashes; commits made
while a host scope was running are not assertions about unchanged launch HEAD.
SCF_015 was the initial focused root audit;016–018 then added source proofs,
which justified the final focused import/axiom audit019. No unchanged full
regression was repeated. Full frozen release closure was NOT rebuilt.

The budget is NOT exhausted. This handoff explicitly stops before adding the
unproved physical clean-transport premise identified above; it does not claim
that a source-proof impossibility or independence theorem has been established.
The task's requested concrete premise removal is incomplete.

No shipped/cfg(kani) file, key/wallet/authority, foreign-prefix module, session
A worktree/candidate or build infrastructure was changed. No binaries/objects/
ELFs/tarballs committed. Thus ELF rebuild trigger did not fire. Inherited pins,
not newly reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

## Final measured result

18/100 actual one-module Lean invocations:12 passes,6 excluded development
failures; one additional dependency-preflight rejection before Lean (004).
0/0 Kani,0 dependency builds. Total compiler wall62.820812889s;
maximum peakRSS5490004KiB;swap0. Budget not exhausted; no100-attempt claim.
All12 current SCF modules match exact-source successful receipts.
Final019 targets SCF_FinalAudit.lean:exit0,wall3.082593463s,
peakRSS5490004KiB,swap0; source anchor8d8dcb63e1 plus exact dirty source hash,
direct dependency object hashes and full printed root/new-theorem axioms.
SCF_HOST_MANIFEST.json pins current own host sources/objects and unchanged
launchers without committing binaries. Offline source/receipt/cap/axiom and
atomic-family recount validation pass; staged and complete branch whitespace
checks pass. No own proof scope remains running after the final returned exit.
