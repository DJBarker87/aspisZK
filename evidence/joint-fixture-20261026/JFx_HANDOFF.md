# Joint accepted fixture: incomplete; source-witness obstruction established

Branch: codex/cx-joint-fixture-20261026. No push. No other worktree edited.

**JFx_Fixture.inhabited is NOT delivered. Target not yet established.**

## Priority finding

`AspisR1.JFx_ExtractionObstruction.cph_fixture_not_extracted` proves:

```
∀ ops hashv,
  ¬ S2W_DigestExtraction.AeneasExtraction
      ops CPH_FixtureData.n1 CPH_FixtureData.n2 hashv
```

The universal stage1 equality (ledger L078) must hold on the empty account list.
CPH's local n1 returns Ok saved there; the source cannot accept it, by the
already proved accepted-call inversion. Thus the existing runtime/game/wrapper
model cannot be extended to the requested full fixture at those SAME natives.
This is a proved inconsistency of that proposed extension, NOT a counterexample
to every possible CPH_Top instance, the deployed implementation, or the existing
runtime-only theorem (which already explicitly excludes source extraction).

The concrete retained native triple and additional checked partial results are
in JFx_STAGE2.md. The source-selected compatibility theorem constructs actual
extracted natives and universal owner laws on one parameterized configuration;
it does not prove those natives accept. None of these results is called the
requested complete non-vacuity theorem.

## Actual-top before/after and recount

CPH_Top.deployed, Rc2_Top.deployed and Rc3_Top.deployed are byte-identical to
this job's entry revision. Full before/after statement sources are retained.
JFx_LEDGER_DELTA.json applies the ledger's atomic quantified-law method,
retaining shared witnesses/guards/carriers: **0 T / 0 P / 0 C delta; 0 premises
removed, 0 added**. The L078 incompatibility is specific to the old CPH model;
it does not change the global ledger's trust classification or premise count.
No security metric, failure event, quantifier, conclusion, source adoption,
runtime trust item or frozen3 adoption was changed.

## Validation

34/100 Lean compile attempts: 25 passed, 9 failed; 0/10 Kani runs. All are
terminal. **The requested whole budget was not exhausted; this handoff is an
incomplete result, not a budget-limit completion.** No claim that the entire
fixture target is mathematically impossible is made. The old-witness extension
is impossible; the alternative actual-source fixture remains an open proof.

Every final JFx_ source hash has a successful focused compile recorded in
JFx_VALIDATION.json, with #print axioms for its new theorems. Only propext,
Classical.choice, Quot.sound occur in accepted final results. Historical error
outputs mentioning sorryAx are rejected attempts, preserved rather than hidden.
Exact target/command/revision/hash/dependencies/exit/wall/RSS/swap/cgroup/axioms
are in each attempt receipt. JFx_REVISION_CORRECTION.json explicitly corrects
four inherited revision labels without changing historical receipts.
Maximum per-attempt peak RSS: 5,334,144 KiB; swaps 0 throughout. Caps were
MemoryHigh6G/MemoryMax8G/SwapMax0/TasksMax64, Lean -M7000. Reservation refusals
were followed by the required waits, never bypassed. No package replay or
unchanged full regression ran. No cap, heartbeat or recursion limit was raised.

Fresh generator --check, literal hash readback, 562-source hash audit and seven
retained receipt hash checks passed. git diff --check passed. No Rust/Kani/SBF
run was needed because shipped files and cfg(kani) harnesses are unchanged.
Default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548
remain inherited artifact pins, not newly reproduced ELF builds.

## Remaining required deliverable

Use the retained literal triple to construct a CLOSED actual source dictionary
and its native/runtime entries, prove BOTH accepted wrappers for those exact
natives and those entries, and derive the frozen3 raw join (or the adopted
charged-collision endpoint) and accepted runtime binding at those SAME witnesses.
Then instantiate the remaining returned continuation/FirstEntry/parser/finish
laws on their actual derived cuts, and compose the owner-approved game and
RuntimePersistence model. No substitute success stubs, assumed accepted cuts,
fixture receipt promoted to a kernel theorem, or rejecting-runtime shortcut
supplies this obligation.

Stage commits:
- 767a65adcb: scope and pins.
- 6314b4473b: checked old-model extraction obstruction.
- 2bcba4d9a0: retained native bytes and checked partial source ports.
