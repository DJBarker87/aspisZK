# SCC handoff: corrected L159 still needs physical observation association

**Target not yet established. L159/L185 remain open. No SCC_Top.deployed,
SCC_Physical.run_eq or SCC_Annotation.transport is claimed.** The task's
explicit stop condition overrides its whole-budget instruction. Branch
`codex/cx-l159-runtime2-20261026`; 3/100 Lean, 0/10 Kani; no push or merge.

## Exact result and minimal missing observation

`SCC_Physical.stored_of_first` derives `StoredInputLaw` from the corrected
`FirstPassBinding`, both exposed in `lean/SCC_Physical.lean` for diagnosis.
Specialized to Rc5's headline prover, the necessary fragment is:

    forall H run,
      (eval H runtime).output = some run -> run.accept = true ->
      run.input.stored =
        (eval H (F3T_Canon.canon (F3T_ByteCarrier.lift c P))).output.stored

The H on both sides is the SAME oracle world. This fragment contains no
virtual replay, security conclusion, or oracle independence assumption. It is
**necessary, not sufficient** for first-pass equality. It is NOT adopted as
runtime trust. The full interface also needs physical public/proof identity,
chronological issued calls, the actual saved checkpoint/history, and association
to the adaptive account experiment. Those are source/experiment refinement
obligations, not consequences of data-only RuntimePersistence.

`SCC_Physical.accepted_unassociated` proves that for EVERY fixed prover P
and world H an unrestricted runtime can return an accepted view whose stored
bytes differ. The witness prepends one byte, returns a constant view with no
oracle calls, and violates FirstPassBinding for EVERY verifier. Thus the
obstruction applies to the installed F3T source as well; `F3T_Installed.old_source`
provides its existing physical-byte identification with DrvC_SourceEntry.source.
No source acceptance is assumed or fabricated in this theorem. This is a
countermodel to an unrestricted observation binder, NOT a deployed attack or
a counterexample to correctness of an actual runtime observer.

Rc5 binds runtime, P, adversary/chooseSecond and the bank projection separately.
Its game fields a-d mention neither runtime nor P; the data persistence law
mentions neither. `CPH_Recorder.physical` relates its own checkpoint bank-action
program to physical events, not the RunView of this runtime/P/account experiment.
`DrvC_PairProgram.source` feeds fixed public/proof and its own TX1 saved bytes to
TX2; the GExq second choice remains adaptive. Their association is not supplied
by the checkpoint game alone. `SCC_Physical.preserve_conditions` explicitly
retains any already satisfied runtime-independent conditions when choosing the
mismatching runtime. It does not assert a full Rc5 joint fixture.

The missing boundary must be filled by constructing the deployed observer and
headline prover from the SAME GExq experiment, then proving their carried-data,
checkpoint/history and oracle chronology correspondence, including rejected
prefixes and adaptive choices. Do not add StoredInputLaw, FirstPassBinding or
ReplayLogLaw to the trust list. Correcting annotation replay does not establish
this logically earlier observation association. Per the explicit STOP instruction,
this job does not spend remaining attempts on annotation wrappers or pretend a
repackaged conditional top removes a premise.

## Before/after and atomic-family recount

Counted root: `AspisR1.Rc5_Top.deployed`. Before/after statements are byte-identical
in `SCC_BEFORE_Top.lean.txt` and `SCC_AFTER_Top.lean.txt`, and match both the
actual root source and its historical Rc5_017 source snapshot. The full current
kernel statement and its body are printed in `SCC_003/stdout.log`. No quantifier,
carrier, failure event, conclusion, accepted guard or shared witness changes.
No assumption is discharged, added, replaced, grouped or reclassified.

`SCC_LEDGER_DELTA.json` retains Rc5's atomic quantified-law-family method:
split conjunctive/structure premises, retain shared dictionaries/guards/witnesses,
exclude output witnesses from input counts, and distinguish deployment aliases.
The offline validator re-enumerates every scope/class/owner subtotal:

- Actual antecedent: **83T/33P/0C -> 83T/33P/0C; delta 0**.
- Deduplicated actual plus non-alias deployment: **89T/46P/0C -> unchanged**.
- All retained audit rows: **89T/48P/0C -> unchanged**.
- L159 remains one actual P family; L185 remains its deployment alias.
- All eleven approved game clauses remain counted. No closure credit is claimed.

## Non-vacuity and validation limits

`SCC_Nonvacuity.game_with_unassociated` combines the concrete existing
`CPH_Nonvacuity.joint_runtime` fixture with the mismatch witness. It retains all
four approved game fields, RuntimePersistence, both successful local wrappers,
and nonempty physical events. The local n1/n2 witnesses do NOT instantiate the
installed cryptographic source or its extraction boundary. This establishes
consistency of the game/runtime conditions with the free-binder obstruction;
it does not inhabit every retained Rc5 premise. No impossible source acceptance
is used, and no fully instantiated deployed forgery is claimed.

Three focused invocations, sequential within this job, used the unchanged
S2W launchers in the coherent SInt2 workspace. Each had -j1 -M7000 and
MemoryHigh=6G/MemoryMax=8G/MemorySwapMax=0/TasksMax=64. Reservation checks allowed
all launches; no waits/retries, timeout, memory kill, cap increase, dependency
build, arithmetic generation, Kani/Rust/SBF build or package replay occurred.

- SCC_001: exit1, 2.287724521s, peakRSS5,285,908KiB, swap0. Ambiguous
  original_eval name; failed elaboration recovery sorryAx output is excluded.
- SCC_002: exit0, 2.340929433s, peakRSS5,312,436KiB, swap0. Qualified
  F3T_TwoPass.original_eval; all four new theorem audits pass.
- SCC_003: exit0, 2.790780244s, peakRSS5,369,820KiB, swap0. New joint
  consistency theorem, fresh audit of all new results, existing CPH fixture
  and actual Rc5 top. All seven audit lines use only
  `[propext, Classical.choice, Quot.sound]`.

Per-attempt receipt.json files include exact target/command, source revision
and dirty-source hashes/snapshots, selected direct object/sidecar fingerprint,
exit, wall, peak RSS, swap, enforced cgroup limits, and full axioms lines;
stdout.log retains complete errors and statement prints. All five new theorem
audits use standard axioms only. No binary/object/archive/ELF is committed.
`SCC_HOST_SOURCES.json` matches both new modules, the relevant runtime/game/
installed-source definitions, Rc5 root, CPH fixture and both unchanged launchers
to local source bytes. Transitive cache provenance remains inherited from
SInt2/Rc5/CPH; these are focused cached checks, not a release closure replay.

`python3 evidence/l159-runtime2-20261026/SCC_validate.py` and
`git diff --check` pass. Total Lean wall7.419434198s; maximumRSS5,369,820KiB;
swap0. Budget unused due to explicit stop: 97 Lean, 10 Kani.

Only SCC_ modules and evidence/l159-runtime2-20261026 changed. No other prefix,
existing proof module, shipped file, cfg(kani) harness, session A worktree/candidate,
key, wallet or funds changed. The ELF rebuild trigger did not fire. Inherited
pins, not newly reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

The 100-bit target remains not established. The next concrete deliverable is
the actual account-experiment observer/prover construction and its same-world
physical source refinement, before any annotation/consumer replacement theorem.
