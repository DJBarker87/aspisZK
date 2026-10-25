# RawK handoff — first-position obstruction

Branch `codex/cx-raw-join2-20261026`. No push. **S2 and the100-bit target remain
unestablished. Ledger premises removed: NONE.** Mandatory decision-(c) stop.

## Checked claim

`AspisR1.RawK_NativeDecision.accepted_pair` (`lean/RawK_NativeDecision.lean`,
RawK_030) starts from the two original accepted native submissions with the
inherited extraction/P1/returning-syscall boundaries. It derives the SAME
`f,s,log`, `SourceCuts` and `RawJ_RecordCuts.Recorded` used by the containing
source caller. `RawK_DecisionWitness.first_difference` (029) gives its actual
source oracle entry at **position0** and proves that every frozen2 decision
has a different entry there, on the SAME H. All model stored/tr/message inputs
are quantified, including any construction from those same f/s/cuts.

The source entry's first byte is85 (`U`), from the actual38-byte
`UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3` domain in semantic initialization.
The complete source address is domain ++ [0] ++ le32(public length) ++
semantic public bytes ++ c1_root, as `RawJ_DigestRead.initParts` defines.
Frozen2's first query is a kind0 leaf at the first sorted batch0 position:
`0x10 :: 0x71 :: (packed ++ salt)`. Its first byte is16. If model admission,
parsing or query decoding exits before batch0, the model log is empty instead.
Thus position0 differs before any checkpoint, duplicate or later query.

`RawK_ModelHead` preserves the original model's batch short-circuiting;
`RawK_ModelAll` handles all initial exits. No rejecting prefix, duplicate,
six repeated checkpoint reads, or later early exit is erased or changed.
`RawK_TraceLogs.ordered` retains the full chronological source child logs;
`RawK_RecordedHead` derives the first child from RawJ's original recorded order,
rather than choosing an independent successful child/log.

## Before/after and ledger delta

Before: RawJ_FramedAccepted supplies the same accepted source pair, complete
containing account log, frames and all-world account envelope. It supplies no
source/frozen2 ordered-log identity. The proposed strict identity was open.

After: from those original native accepted submissions, RawK derives an actual
position0 entry whose address differs from EVERY frozen2 decision's position0.
No equality, model acceptance, parser success, query value, collision exclusion,
start-charge bound, alternate runtime or independently accepted log is added
as a premise. The source return, carriers, inputs and failure event are unchanged.
This is an accepted-run source/model separation theorem, not a security theorem.

| Sub-row | Before | After | Premises removed |
|---|---|---|---|
| (c) ordered-log decision/equality | OPEN | Position0 obstruction checked; equality unavailable on any accepted source run in the retained class | 0 |
| (a) restricted(Q+34) start charge, account envelope Q0+Q1+1921 | OPEN | OPEN; mandatory stop before this work | 0 |
| (b) account-to-Port1 transport | OPEN | OPEN; mandatory stop before this work | 0 |

L157 and L182 at DrvC remain OPEN. No DrvC, other-cone candidate, global ledger,
model or shipped file was edited. No query-reordering transport was attempted.
Owner-level next deliverable: choose the experiment/query-order transport or
model architecture, explicitly accounting for semantic preparation and the
original source log; strict bare dV_frozen2 log equality cannot provide it.

## Non-vacuity and retained boundaries

The first source query and its nonempty containing log are DERIVED from the
original accepted submissions, not stipulated by a new query-existence premise.
The final theorem does not assume that frozen2 accepts or even parses; it covers
every model input. Consequently inconsistent model-acceptance or no-collision
hypotheses cannot make the comparison vacuous. It returns the actual source
query and cuts on every accepted run in the retained native class.

This is a symbolic accepted-run witness, not a newly constructed concrete
fully instantiated SDK/runtime/crypto fixture. No existence or mutual
satisfiability certificate for all deployed retained boundaries is claimed.
That distinction remains explicit; native acceptance and the inherited
AeneasExtraction/P1/syscall boundaries are conditional, as in RawJ. No trust,
cryptographic assumption, carrier, security metric or release target changed.
SDK/std/runtime/allocator and unrelated child-cone obligations remain inherited.

The inherited arithmetic check is retained explicitly:

    2^-108 - 6*(1161^2+2961^2)/2^256 - 2^-126 - 2^-454 > 0.

RawJ_Numeric.zero_margin and margin_positive were imported and axioms-audited
by RawK_Audit; their existing proofs were reused, not rerun/reworked. This
positive margin does not repair the ordered-log obstruction or establish the
restricted start charge/account-to-Port1 transport.

## Validation and freeze

Budget **31/100 charged Lean attempts,0/0 Kani**:30 Lean invocations
(19 exit0,11 excluded development failures), plus own-prerequisite prelaunch016.
No unchanged timed-out/memory-killed rerun, timeout, memory kill, cap increase,
large arithmetic gate, package replay or full frozen manifest replay occurred.
The mismatch stop, rather than budget exhaustion, ends proof development.
Prelaunch016 had no Lean process: RawK_CodeHead was not yet available; its
elaboration was corrected and the dependent source compiled in020. No launcher,
monitor, admission or cache infrastructure was modified.

Every invocation used the unchanged S2W launchers in coherent SInt2, one module,
-j1 -M7000 -DElab.async=false,6G high/8G max/swap0/tasks64. Max peakRSS5254180KiB;
every swap count0. No simultaneous RawK jobs. Final read-only scope inventory
found no RawK scope; another worker's NP6 scope was left untouched.

Final focused audit `RawK_Audit.lean`,031: exit0,wall1.808062889s,
peakRSS5239660KiB,swap0,revision anchor92a57ab9c3 with new audit source dirty;
exact sourceSHA and selected dependency object/sidecar fingerprints are in
RawK_031/receipt.json. All nine final axioms prints use only
[propext,Classical.choice,Quot.sound]. Every new top theorem has its own
successful printed audit, recorded with exact target/command,source snapshot,
SHA,revision,dependency fingerprint,exit,wall,RSS,swap,cgroup and errors.
Failed elaboration recovery prints are retained but excluded from accepted
axiom evidence. RawK_validation-summary.json matches all18 final RawK modules
to exact-source exit0 receipts.

RawK_reused-source-sha256.json checks all187 reused local GExp_/GExq_/RawJ_
source files against the coherent host workspace, all matching. Objects and
historical provenance remain pinned by the inherited SInt2 handoff/manifests
and each invocation's selected direct objects/sidecars. This is focused
verification against that coherent cache, not a fresh release dependency replay.

No shipped/cfg(kani) file changed, so the ELF rebuild trigger did not fire.
Inherited pins, NOT rebuilt or newly validated:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

No Rust,Kani,SBF,key,fund,ELF,binary,object,archive,other worktree or other
worker module changed. Only new RawK_ modules and this evidence directory
changed. Stage commits are local, plain messages, no attribution; no push.
